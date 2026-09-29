-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_emc_of_lambda_or_beta
-- name    : FranklKupavskii2022.EMC.emc_of_lambda_or_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:22:10.808098+00:00
-- url     : https://prove2.me/theorems/12e544d7-0f6f-430b-a6bd-db85c17d4bbf
-- title:
--   Lemma 16: the EMC at $n=s+(c+\varepsilon)s(k-1)$ under (27) or (28)
-- statement:
--   Fix $c=1.666$. For every $\varepsilon>0$ there is $s_0\in\mathbb N$ such that the following holds for every $s\ge s_0$ and every $k\ge2$. Put $n=\lceil s+(c+\varepsilon)s(k-1)\rceil$ and let $\mathcal F\subseteq\binom{[n]}k$ be initial with $\nu(\mathcal F)\le s$. Let $q'$ satisfy $q'|\partial\mathcal F(\emptyset)|=|\mathcal F(\emptyset)|$, and let $\lambda,\beta>0$ satisfy
--
--   $$
--   |\partial\mathcal F(\emptyset)|=\lambda\binom{n-s-1}{k-1},\qquad|\mathcal F(\emptyset)|=\beta\binom{n-s-1}{k}.
--   $$
--
--   If at least one of
--
--   $$
--   \lambda\le\frac{s(c-1)}{q'c}\quad(27)\qquad\text{or}\qquad\beta\le\frac{(c-1)k}{c^2(k-1)}-\varepsilon\quad(28)
--   $$
--
--   holds, then the Erdős Matching Conjecture holds for $\mathcal F$:
--
--   $$
--   |\mathcal F|\le\binom nk-\binom{n-s}k .
--   $$
--
--   The lemma translates Lemma 15 to the matching problem at the critical value of $n$.
--
--   **Formalization Note** $c$ is the exact decimal $1.666$, not $5/3$. The paper omits integer parts; $n$ is rounded up. $k\ge2$ is added since (28) divides by $k-1$. The threshold $s_0$ depends only on $\varepsilon$.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Lemma 16, p. 10

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial
import Definitions.Def_FranklKupavskii2022_EMC_trace

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- Lemma 16 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 10): fix `c = 1.666`. For any `ε > 0` there
exists `s_0 ∈ ℕ` such that the following holds for any `s ≥ s_0`. Put `n = s + (c + ε)s(k − 1)` and
consider an initial family `F ⊂ \binom{[n]}{k}` satisfying `ν(F) ≤ s`. Assume that
`q′|∂F(∅)| = |F(∅)|`, and let `λ, β > 0` be such that `|∂F(∅)| = λ\binom{n−s−1}{k−1}` and
`|F(∅)| = β\binom{n−s−1}{k}`. Then the EMC is true, provided that at least one of
`λ ≤ \frac{s(c−1)}{q′c}` (27) or `β ≤ \frac{(c−1)k}{c²(k−1)} − ε` (28) holds.

**Formalization Note.**
1. `c = 1.666` is the exact decimal `1666/1000`, not `5/3`.
2. The paper omits integer parts (Sect. 4, p. 9); here `n = ⌈s + (c + ε)s(k − 1)⌉`.
3. "The EMC is true" is the conclusion for this family, as the proof ends ("this gives
   |A| ≥ |F|"): `|F| ≤ \binom{n}{k} − \binom{n−s}{k}` (natural subtraction, exact since
   `\binom{n−s}{k} ≤ \binom{n}{k}`).
4. `k ≥ 2` is added: (28) divides by `k − 1`. `s_0` depends on `ε` only and is chosen before `k`.
5. `q′, λ, β` are real numbers bound by the three displayed equations, with `λ, β > 0` as in the
   paper. -/
theorem emc_of_lambda_or_beta (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ k : ℕ, 2 ≤ k → ∀ n : ℕ,
      n = ⌈(s : ℝ) + (1666 / 1000 + ε) * s * ((k : ℝ) - 1)⌉₊ →
      ∀ F : Finset (Finset ℕ), F ⊆ (Finset.Icc 1 n).powersetCard k → IsInitial n k F →
      matchingNumber F ≤ s →
      ∀ q' lam β : ℝ,
        q' * ((∂ (trace s F ∅)).card : ℝ) = ((trace s F ∅).card : ℝ) →
        0 < lam → 0 < β →
        ((∂ (trace s F ∅)).card : ℝ) = lam * ((n - s - 1).choose (k - 1) : ℝ) →
        ((trace s F ∅).card : ℝ) = β * ((n - s - 1).choose k : ℝ) →
        (lam ≤ s * (1666 / 1000 - 1) / (q' * (1666 / 1000)) ∨
          β ≤ (1666 / 1000 - 1) * k / ((1666 / 1000) ^ 2 * ((k : ℝ) - 1)) - ε) →
        F.card ≤ n.choose k - (n - s).choose k := by sorry

end FranklKupavskii2022.EMC
