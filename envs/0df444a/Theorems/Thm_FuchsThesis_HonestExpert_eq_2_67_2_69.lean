-- Prove2me | Theorems.Thm_FuchsThesis_HonestExpert_eq_2_67_2_69
-- name    : FuchsThesis.HonestExpert.eq_2_67_2_69
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:21.683224+00:00
-- url     : https://prove2.me/theorems/6d86c3b3-4aed-4dcf-b861-b5b16fca64e6
-- title:
--   (2.67)–(2.69) — two honest payoffs are $\alpha\ln p+\gamma_k$ with a common $\alpha\ge 0$
-- statement:
--   Let $n \ge 3$, let $F_1, \dots, F_n$ keep the expert honest and let $i \ne j$ be two outcomes. Then there are real constants $\alpha \ge 0$, $\gamma_i$ and $\gamma_j$ such that for every $p \in (0, 1)$:
--
--   1. $F_i$ and $F_j$ are differentiable at $p$ and $p\,F_i'(p) = p\,F_j'(p) = \alpha$ ((2.67)–(2.68));
--   2. $$F_i(p) = \alpha \ln p + \gamma_i, \qquad F_j(p) = \alpha \ln p + \gamma_j \qquad (2.69).$$
--
--   This is the "only if" half of Theorem 2.3 for one pair of outcomes; running it over all pairs $(1, k)$ yields the common $\alpha$ for all $n$ payoffs.
--
--   Differences from the source:
--   - generalization: the outcomes 1 and 2 → any two distinct outcomes i ≠ j; reason: p.24 runs the same argument for the pair (1, k); i = 1, j = 2 gives the page's case
--   - reading: (2.45) for all n-point distributions, conclusions for p in the domain [0, 1] → (2.45) for all strictly positive n-point distributions, conclusions for p ∈ (0, 1); reason: ln p is undefined at 0, and (0, 1) is the range of the coordinates of positive distributions for n ≥ 3 (the positivity reading of Theorem 2.3)
--   - encoding: ln → Real.log (natural logarithm); outcomes 1, …, n → Fin n; reason: Lean conventions
--   - encoding: real payoffs F_k defined on [0, 1] → real functions F_k defined on all of ℝ; reason: only values on (0, 1) enter (the coordinates of strictly positive distributions for n ≥ 3); any F_k on [0, 1] extends to ℝ and the extension changes no clause
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.3.1, eqs. (2.67)–(2.69), p.23 (PDF p.32)

import Mathlib
import Definitions.Def_FuchsThesis_HonestExpert_KeepsHonest

namespace FuchsThesis.HonestExpert

/-- **(2.67)–(2.69): two honest payoffs are logarithms with a common nonnegative coefficient.**
Fuchs, *Distinguishability and Accessible Information in Quantum Theory*, arXiv:quant-ph/9601020v1,
§2.3.1, eqs. (2.67)–(2.69), p.23 (PDF p.32): "there must be a constant α such that
p F₁′(p) = s F₂′(s) = α. Because F₁ and F₂ are monotonically nondecreasing, α ≥ 0. So
F₁′(p) = α/p and F₂′(p) = α/p; integrating this we get F₁(p) = α ln p + γ₁ and
F₂(p) = α ln p + γ₂ where γ₁ and γ₂ are integration constants."

For `n ≥ 3`, payoffs `F` keeping the expert honest and outcomes `i ≠ j` (the page's `1, 2`), there
are reals `α ≥ 0`, `γ_i`, `γ_j` such that for every `p ∈ (0, 1)`:
`F_i` and `F_j` are differentiable at `p` with `p F_i′(p) = p F_j′(p) = α` ((2.67)–(2.68)), and
`F_i(p) = α ln p + γ_i`, `F_j(p) = α ln p + γ_j` ((2.69)).

**Formalization Note.** `ln` is `Real.log` (natural logarithm); `p` ranges over the open interval
`(0, 1)`, where the logarithm is defined and which is the range of the coordinates of strictly
positive distributions. -/
theorem eq_2_67_2_69 {n : ℕ} (hn : 3 ≤ n) {F : Fin n → ℝ → ℝ} (hF : KeepsHonest F)
    {i j : Fin n} (hij : i ≠ j) :
    ∃ α : ℝ, 0 ≤ α ∧ ∃ γi γj : ℝ, ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (F i) p ∧ DifferentiableAt ℝ (F j) p ∧
        p * deriv (F i) p = α ∧ p * deriv (F j) p = α ∧
        F i p = α * Real.log p + γi ∧ F j p = α * Real.log p + γj := by sorry

end FuchsThesis.HonestExpert
