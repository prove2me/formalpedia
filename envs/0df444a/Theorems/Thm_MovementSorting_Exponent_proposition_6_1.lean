-- Prove2me | Theorems.Thm_MovementSorting_Exponent_proposition_6_1
-- name    : MovementSorting.Exponent.proposition_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:01:34.419935+00:00
-- url     : https://prove2.me/theorems/83f9acfd-2f62-440d-939a-5cd92ed41235
-- title:
--   Proposition 6.1 — for d ≥ 2: M_1 = O_d(n²) deterministically, M_2 = O_d(n^{(6d−1)/(4d−1)})
-- statement:
--   Let $d \ge 2$. There are $C > 0$ and $m_0$ depending only on $d$ such that for every $m \ge m_0$: (i) some valid deterministic $1$-round algorithm has $\mathrm{Move} \le C n^2$ on every input, and $M^{(d)}_1(n) \le C n^2$; (ii) $M^{(d)}_2(n) \le C n^{\beta^{(d)}_2}$; and $\beta^{(d)}_2 = (6d-1)/(4d-1)$.
--
--   Differences from the source:
--   - encoding: asymptotic symbols Ω / O / Θ with the stated subscripts, n → ∞ → explicit constants (c > 0 or C > 0) quantified with exactly the stated dependencies, and a threshold m₀ with the bound for every m ≥ m₀, n = m^d (nR d m); reason: the model is defined only at n = m^d; the constants are uniform in m as the notation of p. 8 requires
--   - encoding: M^{(d)}_r(n) = inf_ALG max_π E[Move(ALG, π)] over randomized r-round algorithms correct for every input and coin outcome → M d r m ∈ ℝ≥0∞: ⨅ over PMFs on valid (well-formed, correct) deterministic r-round algorithms of ⨆ over inputs π of Σ μ(A)·Move(A, π); Minf d m = ⨅ over r ≥ 1; reason: Definition 2.1 with the coins fixed in advance; ℝ≥0∞ makes the infimum over an empty class +∞ instead of a junk 0, and countable-support coin distributions are the paper's algorithms
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Proposition 6.1, p. 29

import Definitions.Def_MovementSorting_Exponent_Model
import Definitions.Def_MovementSorting_Exponent_Beta

set_option autoImplicit false

namespace MovementSorting.Exponent

/-- Proposition 6.1 (p. 29): let `d ≥ 2`. (i) `M^{(d)}_1(n) = O_d(n^2)`, attained by a
deterministic algorithm; (ii) `M^{(d)}_2(n) = O_d(n^{β^{(d)}_2})` with `β^{(d)}_2 = (6d-1)/(4d-1)`. -/
theorem proposition_6_1 :
    ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ((∃ A : DetAlg d m 1, IsValidAlg A ∧ ∀ π : Input d m, (A.move π : ℝ) ≤ C * nR d m ^ 2) ∧
        M d 1 m ≤ ENNReal.ofReal (C * nR d m ^ 2)) ∧
      M d 2 m ≤ ENNReal.ofReal (C * nR d m ^ beta d 2) ∧
      beta d 2 = (6 * d - 1 : ℝ) / (4 * d - 1) := by sorry

end MovementSorting.Exponent
