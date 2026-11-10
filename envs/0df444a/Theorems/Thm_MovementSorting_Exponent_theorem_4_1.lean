-- Prove2me | Theorems.Thm_MovementSorting_Exponent_theorem_4_1
-- name    : MovementSorting.Exponent.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:01:26.004066+00:00
-- url     : https://prove2.me/theorems/53fd3e8c-2682-45b9-970e-f5f2b2525d5c
-- title:
--   Theorem 4.1 — lower bound M^{(d)}_r(n) = Ω_{d,r}(n^{β^{(d)}_r}/log n)
-- statement:
--   For every $d \ge 1$ and finite $r \ge 1$ there are $c > 0$ and $m_0$ depending only on $d$ and $r$ such that $M^{(d)}_r(n) \ge c\, n^{\beta^{(d)}_r}/\log_2 n$ for every $m \ge m_0$, $n = m^d$.
--
--   Differences from the source:
--   - encoding: asymptotic symbols Ω / O / Θ with the stated subscripts, n → ∞ → explicit constants (c > 0 or C > 0) quantified with exactly the stated dependencies, and a threshold m₀ with the bound for every m ≥ m₀, n = m^d (nR d m); reason: the model is defined only at n = m^d; the constants are uniform in m as the notation of p. 8 requires
--   - encoding: M^{(d)}_r(n) = inf_ALG max_π E[Move(ALG, π)] over randomized r-round algorithms correct for every input and coin outcome → M d r m ∈ ℝ≥0∞: ⨅ over PMFs on valid (well-formed, correct) deterministic r-round algorithms of ⨆ over inputs π of Σ μ(A)·Move(A, π); Minf d m = ⨅ over r ≥ 1; reason: Definition 2.1 with the coins fixed in advance; ℝ≥0∞ makes the infimum over an empty class +∞ instead of a junk 0, and countable-support coin distributions are the paper's algorithms
--   - encoding: log n (base 2) → Real.logb 2 (nR d m); reason: the paper fixes base 2 (p. 8); n ≥ 2 so the logarithm is positive
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Theorem 4.1, p. 12

import Definitions.Def_MovementSorting_Exponent_Model
import Definitions.Def_MovementSorting_Exponent_Beta

set_option autoImplicit false

namespace MovementSorting.Exponent

/-- Theorem 4.1 (Lower Bound, p. 12): for every fixed `d ≥ 1` and `r ≥ 1`,
`M^{(d)}_r(n) = Ω_{d,r}(n^{β^{(d)}_r} / log n)`. -/
theorem theorem_4_1 :
    ∀ d r : ℕ, 1 ≤ d → 1 ≤ r → ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ENNReal.ofReal (c * nR d m ^ beta d r / Real.logb 2 (nR d m)) ≤ M d r m := by sorry

end MovementSorting.Exponent
