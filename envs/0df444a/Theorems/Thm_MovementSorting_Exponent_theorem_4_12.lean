-- Prove2me | Theorems.Thm_MovementSorting_Exponent_theorem_4_12
-- name    : MovementSorting.Exponent.theorem_4_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:01:45.515502+00:00
-- url     : https://prove2.me/theorems/dd33c3fd-37c3-48a5-bf99-dcd68ea1b7c9
-- title:
--   Theorem 4.12 — exact lower bound on the line: M^{(1)}_r(n) = Ω_r(n^{β_r})
-- statement:
--   For $d = 1$ and every finite $r \ge 1$ there are $c > 0$ and $m_0$ depending only on $r$ such that $M^{(1)}_r(n) \ge c\,n^{\beta_r}$ for every $m \ge m_0$ ($n = m$).
--
--   Differences from the source:
--   - encoding: asymptotic symbols Ω / O / Θ with the stated subscripts, n → ∞ → explicit constants (c > 0 or C > 0) quantified with exactly the stated dependencies, and a threshold m₀ with the bound for every m ≥ m₀, n = m^d (nR d m); reason: the model is defined only at n = m^d; the constants are uniform in m as the notation of p. 8 requires
--   - encoding: M^{(d)}_r(n) = inf_ALG max_π E[Move(ALG, π)] over randomized r-round algorithms correct for every input and coin outcome → M d r m ∈ ℝ≥0∞: ⨅ over PMFs on valid (well-formed, correct) deterministic r-round algorithms of ⨆ over inputs π of Σ μ(A)·Move(A, π); Minf d m = ⨅ over r ≥ 1; reason: Definition 2.1 with the coins fixed in advance; ℝ≥0∞ makes the infimum over an empty class +∞ instead of a junk 0, and countable-support coin distributions are the paper's algorithms
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Theorem 4.12, p. 19

import Definitions.Def_MovementSorting_Exponent_Model
import Definitions.Def_MovementSorting_Exponent_Beta

set_option autoImplicit false

namespace MovementSorting.Exponent

/-- Theorem 4.12 (p. 19): for `d = 1` and every fixed `r ≥ 1`, `M^{(1)}_r(n) = Ω_r(n^{β_r})`. -/
theorem theorem_4_12 :
    ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ENNReal.ofReal (c * nR 1 m ^ beta 1 r) ≤ M 1 r m := by sorry

end MovementSorting.Exponent
