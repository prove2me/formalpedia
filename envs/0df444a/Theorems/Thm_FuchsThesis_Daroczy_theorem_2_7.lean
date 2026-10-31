-- Prove2me | Theorems.Thm_FuchsThesis_Daroczy_theorem_2_7
-- name    : FuchsThesis.Daroczy.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:48.653601+00:00
-- url     : https://prove2.me/theorems/7983bb0c-6dfa-4adc-b30e-13f6dee238f8
-- title:
--   Theorem 2.7 (Daróczy): the limit $\alpha\to1$ of $H_\alpha$ is the Shannon entropy
-- statement:
--   For each real $\alpha > 0$ with $\alpha \ne 1$ let $H_\alpha : \Gamma \to \mathbb R$ be a function on the discrete probability distributions $\Gamma = \bigcup_n \Gamma_n$ which is symmetric in all its arguments and satisfies, for each $n \ge 2$, the recursion
--
--   $$
--   H_\alpha(p_1,\dots,p_n) = H_\alpha(p_1+p_2, p_3,\dots,p_n) + (p_1+p_2)^{\alpha}\, H_\alpha\!\left(\frac{p_1}{p_1+p_2}, \frac{p_2}{p_1+p_2}\right). \tag{2.111}
--   $$
--
--   Suppose $H_\alpha(\tfrac12, \tfrac12) \to C$ as $\alpha \to 1$. Then for every $n$ and every $(p_1,\dots,p_n) \in \Gamma_n$,
--
--   $$
--   \lim_{\alpha \to 1} H_\alpha(p_1,\dots,p_n) = -\frac{C}{\ln 2} \sum_{i=1}^{n} p_i \ln p_i ,
--   $$
--
--   with the convention $0 \ln 0 = 0$.
--
--   Symmetry and the recursion (an "objectivity" requirement: the information gained does not depend on the order in which the outcome is queried) thus determine the Shannon information function up to the choice of units $C$: $C = 1$ gives bits, $C = \ln 2$ gives nats.
--
--   **Formalization Note** The limit is taken along real $\alpha \ne 1$ tending to $1$. $\ln 0 = 0$ in Lean, which gives the convention $0 \ln 0 = 0$.
--
--   Differences from the source:
--   - reading: "the limiting value of $H_\alpha$ as $\alpha \to 1$ is uniquely specified up to a constant $C$" → if $H_\alpha(\tfrac12,\tfrac12) \to C$ then $H_\alpha(p) \to -\tfrac{C}{\ln 2}\sum_i p_i \ln p_i$ for every $p \in \Gamma$; reason: the proof gives $H_\alpha = C_\alpha(2^{1-\alpha}-1)^{-1}(\sum_i p_i^\alpha - 1)$ with $C_\alpha = H_\alpha(\tfrac12,\tfrac12)$ depending on $\alpha$; a family with $C_\alpha = C$ constant is a special case of this reading
--   - encoding: recursion (2.111) for every $n \ge 2$ → recursion required only when $p_1 + p_2 > 0$; reason: the right side of (2.111) is undefined at $p_1 + p_2 = 0$, so this only excludes undefined cases
--   - encoding: $\alpha \to 1$ → limit along the punctured neighbourhood filter of $1$; reason: $H_\alpha$ is given only for $\alpha \ne 1$, and every punctured neighbourhood of $1$ eventually lies in $(0,\infty)\setminus\{1\}$
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Theorem 2.7 (Daróczy), eqs. (2.111)–(2.113), p.32 (PDF p.41); proof pp.32–35 (PDF pp.41–44)

import Mathlib
import Definitions.Def_FuchsThesis_Daroczy_IsDist
import Definitions.Def_FuchsThesis_Daroczy_IsSymmetric
import Definitions.Def_FuchsThesis_Daroczy_SatisfiesRecursion

namespace FuchsThesis.Daroczy

open Filter Topology

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Theorem 2.7 (Daróczy), eqs. (2.111)–(2.113), p.32 (PDF p.41), proved
on pp.32–35: let `(H_α)` be a family of functions on the discrete probability distributions
`Γ = ⋃ₙ Γₙ`, indexed by the positive parameters `α ≠ 1`, each symmetric in all its arguments
and satisfying (2.111) for each `n ≥ 2`. Then, under the convention `0 ln 0 = 0`, the limiting
value of `H_α` as `α → 1` is uniquely specified up to a constant `C` by
`H(p₁, …, pₙ) = −(C / ln 2) ∑_{i=1}^{n} p_i ln p_i` (2.113).

**Formalization Note.** Reading of "up to a constant C": the proof shows `H_α = C_α (2^{1−α} −
1)^{−1}(∑ p_i^α − 1)` with `C_α = H_α(1/2, 1/2)` (2.130), so the statement is: if
`H_α(1/2, 1/2) → C` as `α → 1`, then `H_α(p) → −(C / ln 2) ∑ p_i ln p_i` for every `p ∈ Γₙ`
and every `n`. A family with `H_α(1/2, 1/2) = C` for all `α` is a special case. The limit is
along `𝓝[≠] 1`; the hypotheses are imposed for every `α > 0, α ≠ 1`, which contains a punctured
neighbourhood of `1`. `Real.log 0 = 0` gives `0 ln 0 = 0`. -/
theorem theorem_2_7 (H : ℝ → (n : ℕ) → (Fin n → ℝ) → ℝ)
    (hsym : ∀ α : ℝ, 0 < α → α ≠ 1 → IsSymmetric (H α))
    (hrec : ∀ α : ℝ, 0 < α → α ≠ 1 → SatisfiesRecursion α (H α))
    (C : ℝ) (hC : Tendsto (fun α => H α 2 ![1 / 2, 1 - 1 / 2]) (𝓝[≠] 1) (𝓝 C))
    (n : ℕ) (p : Fin n → ℝ) (hp : IsDist p) :
    Tendsto (fun α => H α n p) (𝓝[≠] 1)
      (𝓝 (-(C / Real.log 2) * ∑ i, p i * Real.log (p i))) := by sorry

end FuchsThesis.Daroczy
