-- Prove2me | Theorems.Thm_HardyFLocal_eq21_pair_expansion
-- name    : HardyFLocal.eq21_pair_expansion
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:39:15.747564+00:00
-- url     : https://prove2.me/theorems/c928c053-417d-4fc6-baba-13fcc393501f
-- title:
--   Eq. (21), p.13 — the pair expansion
-- statement:
--   Let $\$_k$ be a fiducial family. For labels $l',l$,
--   $$\$_{l'}\circ\$_l=\sum_{k\in\Omega^2}\Lambda^{1k}_{l'l}\,\$_k,$$
--   with real coefficients that are unique. Since $\$_1=I$, the same expansion can be written in the printed form, as a sum over $\{1\}\times\Omega^2$ of $\$_{k'}\circ\$_k$.
--
--   This pair table is the second object specifying the causaloid.
--
--   Differences from the source:
--   - reading: a "fiducial spanning set of superoperators", with Λ in "a real vector space" (p.9) → a basis over ℝ of the Hermiticity-preserving one-qubit maps; reason: real coefficients are what p.9 requires, and they exist for Hermiticity-preserving maps
--   - encoding: labels run from 1, and the first element of Ω² is 1 → labels are 0-based, and the first element of Ω² = Fin 16 is 0; reason: Lean convention; same instances
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, eq. (21), p.13

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_FiducialFamily

set_option autoImplicit false

namespace HardyFLocal

/-- **Eq. (21): the pair expansion**, Hardy, arXiv:0804.0054v1, §5, eq. (21), p.13 ("But this is a
superoperator belonging to the space of superoperators acting on a single qubit and can, hence, be
expanded in terms of the linearly independent fiducial set").

For all `l', l`, the composite `$_{l'} ∘ $_l` is `Σ_k Λ^{1 k}_{l' l} $_k` with `Λ = pairTable S`,
the real coefficients are unique, and the same expansion holds in the printed form, as a sum over
`{1} × Ω²` of `$_{k'} ∘ $_k`. -/
theorem eq21_pair_expansion (S : FiducialFamily) (l' l : Ω) :
    S.map l' ∘ₗ S.map l = ∑ k, pairTable S l' l k • S.map k ∧
    (∀ c : Ω → ℝ, S.map l' ∘ₗ S.map l = ∑ k, c k • S.map k → c = pairTable S l' l) ∧
    S.map l' ∘ₗ S.map l = ∑ p ∈ ({0} : Finset Ω) ×ˢ (Finset.univ : Finset Ω),
      pairTable S l' l p.2 • (S.map p.1 ∘ₗ S.map p.2) := by sorry

end HardyFLocal
