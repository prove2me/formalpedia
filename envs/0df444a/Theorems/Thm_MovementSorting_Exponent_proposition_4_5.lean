-- Prove2me | Theorems.Thm_MovementSorting_Exponent_proposition_4_5
-- name    : MovementSorting.Exponent.proposition_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:01:35.785582+00:00
-- url     : https://prove2.me/theorems/c07d4091-0901-4a96-aa4a-1af400e5bed4
-- title:
--   Proposition 4.5 — M^{(d)}_r(n) = Ω_d(n^{1+1/(2d)}) for every r, including r = ∞
-- statement:
--   For every $d \ge 1$ there are $c > 0$ and $m_0$ depending only on $d$ such that for every $m \ge m_0$: $M^{(d)}_r(n) \ge c\,n^{1+1/(2d)}$ for every finite $r \ge 1$ (one constant for all $r$), and $M^{(d)}_\infty(n) \ge c\,n^{1+1/(2d)}$.
--
--   Differences from the source:
--   - encoding: asymptotic symbols Ω / O / Θ with the stated subscripts, n → ∞ → explicit constants (c > 0 or C > 0) quantified with exactly the stated dependencies, and a threshold m₀ with the bound for every m ≥ m₀, n = m^d (nR d m); reason: the model is defined only at n = m^d; the constants are uniform in m as the notation of p. 8 requires
--   - encoding: M^{(d)}_r(n) = inf_ALG max_π E[Move(ALG, π)] over randomized r-round algorithms correct for every input and coin outcome → M d r m ∈ ℝ≥0∞: ⨅ over PMFs on valid (well-formed, correct) deterministic r-round algorithms of ⨆ over inputs π of Σ μ(A)·Move(A, π); Minf d m = ⨅ over r ≥ 1; reason: Definition 2.1 with the coins fixed in advance; ℝ≥0∞ makes the infimum over an empty class +∞ instead of a junk 0, and countable-support coin distributions are the paper's algorithms
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Proposition 4.5, p. 15

import Definitions.Def_MovementSorting_Exponent_Model

set_option autoImplicit false

namespace MovementSorting.Exponent

/-- Proposition 4.5 (p. 15): for every fixed `d` and every `r`, including `r = ∞`,
`M^{(d)}_r(n) = Ω_d(n^{1+1/(2d)})`, with one constant for all `r`. -/
theorem proposition_4_5 :
    ∀ d : ℕ, 1 ≤ d → ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (∀ r : ℕ, 1 ≤ r → ENNReal.ofReal (c * nR d m ^ (1 + 1 / (2 * d : ℝ))) ≤ M d r m) ∧
      ENNReal.ofReal (c * nR d m ^ (1 + 1 / (2 * d : ℝ))) ≤ Minf d m := by sorry

end MovementSorting.Exponent
