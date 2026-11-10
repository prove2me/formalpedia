-- Prove2me | Theorems.Thm_MovementSorting_Exponent_proposition_4_4
-- name    : MovementSorting.Exponent.proposition_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:02:09.623935+00:00
-- url     : https://prove2.me/theorems/032bd7d4-7b34-4662-83f1-ceec810723bc
-- title:
--   Proposition 4.4 — for r ≤ 2, M^{(d)}_r(n) = Ω_d(n^{β^{(d)}_r})
-- statement:
--   For every $d \ge 1$ there are $c > 0$ and $m_0$ depending only on $d$ such that for $r \in \{1,2\}$ and every $m \ge m_0$, $M^{(d)}_r(n) \ge c\, n^{\beta^{(d)}_r}$, $n = m^d$.
--
--   Differences from the source:
--   - encoding: asymptotic symbols Ω / O / Θ with the stated subscripts, n → ∞ → explicit constants (c > 0 or C > 0) quantified with exactly the stated dependencies, and a threshold m₀ with the bound for every m ≥ m₀, n = m^d (nR d m); reason: the model is defined only at n = m^d; the constants are uniform in m as the notation of p. 8 requires
--   - encoding: M^{(d)}_r(n) = inf_ALG max_π E[Move(ALG, π)] over randomized r-round algorithms correct for every input and coin outcome → M d r m ∈ ℝ≥0∞: ⨅ over PMFs on valid (well-formed, correct) deterministic r-round algorithms of ⨆ over inputs π of Σ μ(A)·Move(A, π); Minf d m = ⨅ over r ≥ 1; reason: Definition 2.1 with the coins fixed in advance; ℝ≥0∞ makes the infimum over an empty class +∞ instead of a junk 0, and countable-support coin distributions are the paper's algorithms
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Proposition 4.4, p. 14

import Definitions.Def_MovementSorting_Exponent_Model
import Definitions.Def_MovementSorting_Exponent_Beta

set_option autoImplicit false

namespace MovementSorting.Exponent

/-- Proposition 4.4 (p. 14): for every fixed `d` and every `r ≤ 2`,
`M^{(d)}_r(n) = Ω_d(n^{β^{(d)}_r})` (constant depending on `d` only). -/
theorem proposition_4_4 :
    ∀ d : ℕ, 1 ≤ d → ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ r : ℕ, 1 ≤ r → r ≤ 2 →
      ∀ m : ℕ, m₀ ≤ m → ENNReal.ofReal (c * nR d m ^ beta d r) ≤ M d r m := by sorry

end MovementSorting.Exponent
