-- Prove2me | Theorems.Thm_HardyFLocal_eq25_26_single_vertex
-- name    : HardyFLocal.eq25_26_single_vertex
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:39:06.31688+00:00
-- url     : https://prove2.me/theorems/a7915bd2-8888-48e1-93c1-752e4bd7a5f4
-- title:
--   Eqs. (25)–(26), p.13 — a clump of one vertex
-- statement:
--   Let $\$_k$ be a fiducial family. For a label $l$,
--   $$\$_l=\sum_{k\in\Omega^2}\Lambda^{k}_{l}\,\$_k,\qquad \Lambda^k_l=\delta^k_l,$$
--   this is the coordinate vector of $\$_l$, and the chain recursion returns the same vector on a one-vertex list, for any tables.
--
--   This is the base case of step 2 of the clumping method.
--
--   Differences from the source:
--   - reading: a "fiducial spanning set of superoperators", with Λ in "a real vector space" (p.9) → a basis over ℝ of the Hermiticity-preserving one-qubit maps; reason: real coefficients are what p.9 requires, and they exist for Hermiticity-preserving maps
--   - encoding: labels run from 1, and the first element of Ω² is 1 → labels are 0-based, and the first element of Ω² = Fin 16 is 0; reason: Lean convention; same instances
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, eqs. (25)–(26), p.13

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_FiducialFamily

set_option autoImplicit false

namespace HardyFLocal

/-- **Eqs. (25)–(26): a clump of one vertex**, Hardy, arXiv:0804.0054v1, §5, eqs. (25)–(26), p.13
("We may have need of the matrix Λ^{k_u}_{l_u} … for a single vertex for a right moving qubit").

`$_l = Σ_k Λ^k_l $_k` holds with `Λ^k_l = δ^k_l`, this is the only such expansion, and the recursion
`chain` returns it on a one-vertex list, for any tables. -/
theorem eq25_26_single_vertex (S : FiducialFamily) (l : Ω) :
    S.map l = ∑ k, (Pi.single l 1 : Ω → ℝ) k • S.map k ∧
    coordsOf S.map (S.map l) = Pi.single l 1 ∧
    ∀ {V : Type} (T : V → V → PairTable) (x : V), chain T [(x, l)] = Pi.single l 1 := by sorry

end HardyFLocal
