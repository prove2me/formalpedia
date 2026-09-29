-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_lambda_or_beta_bound
-- name    : FranklKupavskii2022.EMC.lambda_or_beta_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:22:50.485906+00:00
-- url     : https://prove2.me/theorems/7eb6f6d0-5ee8-48fc-aed1-01e51311a37e
-- title:
--   Lemma 17: for $c=1.666$ one of (27), (28) holds
-- statement:
--   Let $c=1.666$. There is $\varepsilon_0>0$ such that for every $0<\varepsilon\le\varepsilon_0$ there is $s_0$ with the following property for every $s\ge s_0$ and every $k\ge4$. Put $n=\lceil s+(c+\varepsilon)s(k-1)\rceil$ and assume the induction hypothesis
--
--   $$
--   m(n-s-1,\,k-1,\,s)=\binom{n-s-1}{k-1}-\binom{n-2s-1}{k-1}.
--   $$
--
--   Let $\mathcal F\subseteq\binom{[n]}k$ be initial with $\nu(\mathcal F)\le s$, and let $q',\lambda,\beta$ be as in Lemma 16 ($q'|\partial\mathcal F(\emptyset)|=|\mathcal F(\emptyset)|$, $|\partial\mathcal F(\emptyset)|=\lambda\binom{n-s-1}{k-1}$, $|\mathcal F(\emptyset)|=\beta\binom{n-s-1}{k}$, $\lambda,\beta>0$). Then
--
--   $$
--   \lambda\le\frac{s(c-1)}{q'c}\qquad\text{or}\qquad\beta\le\frac{(c-1)k}{c^2(k-1)}-\varepsilon .
--   $$
--
--   Combined with Lemma 16 this completes the induction step of Theorem 14. The proof combines the layer decomposition of Section 2.1 with numerical estimates of sums of binomial coefficients, verified in the paper with computer algebra.
--
--   **Formalization Note** The paper states the lemma in one line inside the induction on $k$; its hypotheses are those named in the appendix (§10.2): the induction hypothesis for $(k-1)$-sets on $n-s-1$ points, $k\ge4$ (the case $k=3$ is an external base case), and $\varepsilon$ small (the appendix works with a margin $\delta=10^{-6}$).
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Lemma 17, p. 11; proof in Appendix §10.2, pp. 24–27

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_emcMax
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial
import Definitions.Def_FranklKupavskii2022_EMC_trace

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- Lemma 17 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 11; proof in Appendix §10, pp. 23–27): for
`c = 1.666` either (27) or (28) is valid, in the setting of Lemma 16 (`n = s + (c + ε)s(k − 1)`,
`F ⊂ \binom{[n]}{k}` initial with `ν(F) ≤ s`, `q′|∂F(∅)| = |F(∅)|`,
`|∂F(∅)| = λ\binom{n−s−1}{k−1}`, `|F(∅)| = β\binom{n−s−1}{k}`, `λ, β > 0`):
`λ ≤ \frac{s(c−1)}{q′c}` (27) or `β ≤ \frac{(c−1)k}{c²(k−1)} − ε` (28).

**Formalization Note.** The one-line statement lives inside the induction on `k` of Sect. 4; its
implicit hypotheses, named in §10.2 (p. 24), are binders:
1. the induction hypothesis: "the EMC holds for m := n − s − 1 = (c + ε)s(k − 1) − 1 and sets of
   size k − 1", i.e. `m(n − s − 1, k − 1, s) = \binom{n−s−1}{k−1} − \binom{n−2s−1}{k−1}`;
2. `k ≥ 4`: the appendix treats `4 ≤ k` (the case `k = 3` is the external base case [16]);
3. `ε` small: the appendix proves (56) with a margin `δ` (say `10^{-6}`), which gives (28) only
   for `ε ≤ δ`; the statement asserts some `ε₀ > 0` such that the lemma holds for `0 < ε ≤ ε₀`,
   with `s_0` depending on `ε` only and chosen before `k`.
`c = 1666/1000` exactly; `n = ⌈s + (c + ε)s(k − 1)⌉` as in Lemma 16. -/
theorem lambda_or_beta_bound :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ k : ℕ, 4 ≤ k → ∀ n : ℕ,
        n = ⌈(s : ℝ) + (1666 / 1000 + ε) * s * ((k : ℝ) - 1)⌉₊ →
        emcMax (n - s - 1) (k - 1) s =
          (n - s - 1).choose (k - 1) - (n - s - 1 - s).choose (k - 1) →
        ∀ F : Finset (Finset ℕ), F ⊆ (Finset.Icc 1 n).powersetCard k → IsInitial n k F →
        matchingNumber F ≤ s →
        ∀ q' lam β : ℝ,
          q' * ((∂ (trace s F ∅)).card : ℝ) = ((trace s F ∅).card : ℝ) →
          0 < lam → 0 < β →
          ((∂ (trace s F ∅)).card : ℝ) = lam * ((n - s - 1).choose (k - 1) : ℝ) →
          ((trace s F ∅).card : ℝ) = β * ((n - s - 1).choose k : ℝ) →
          lam ≤ s * (1666 / 1000 - 1) / (q' * (1666 / 1000)) ∨
            β ≤ (1666 / 1000 - 1) * k / ((1666 / 1000) ^ 2 * ((k : ℝ) - 1)) - ε := by sorry

end FranklKupavskii2022.EMC
