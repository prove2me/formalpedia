-- Prove2me | Theorems.Thm_GaloisRep_not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar
-- name    : GaloisRep.not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/d941f277-d555-55c0-9d6d-d8d34cb3f196
-- title:
--   No irreducible mod 3 representation unramified outside 3
-- statement:
--   Let $\rho$ be a group homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\mathrm{GL}_2(\mathbb{Z}/3)$. Assume: (i) there is an intermediate field $M$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, whose fixing subgroup is contained in $\ker\rho$ (so $\rho$ has open kernel); (ii) $\rho$ is unramified at every prime $q \neq 3$, in the sense that for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ (pushed forward along the inclusion of the decomposition subgroup) lies in $\ker\rho$; (iii) the composite of $\rho$ with the determinant $\mathrm{GL}_2(\mathbb{Z}/3) \to (\mathbb{Z}/3)^\times$ equals [`WeierstrassCurve.modThreeCyclotomicChar`](def/GaloisRep_ModThreeCyclotomic.html#L10), the character given by the modular cyclotomic character of $\overline{\mathbb{Q}}$ at $3$. Then the associated representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $\mathrm{Fin}\,2 \to \mathbb{Z}/3$, obtained from $\rho$ by regarding invertible matrices as linear automorphisms, is not irreducible.
--
--   This is the level-one exclusion at $p = 3$: there is no irreducible two-dimensional mod $3$ representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of conductor $1$ with cyclotomic determinant, the analogue for $p=3$ of Tate's non-existence theorem at $p=2$. It is used on the elliptic-curve side of the argument: for a semistable $E/\mathbb{Q}$ with $\bar\rho_{E,3}$ irreducible it forces some inertia group at a prime $q \neq 3$ to act non-trivially on $E[3]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar.lean

import Mathlib
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_GaloisRep_ModThreeCyclotomic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (hM : FiniteDimensional ℚ M)
    (hker : M.fixingSubgroup ≤ ρ.ker)
    (hunr : ∀ q : ℕ, q.Prime → q ≠ 3 → GlobalGaloisRep.IsUnramifiedAt ρ q)
    (hdet : Matrix.GeneralLinearGroup.det.comp ρ = WeierstrassCurve.modThreeCyclotomicChar) :
    ¬ Representation.IsIrreducible (Deformation.matrixRepresentation ρ) := by sorry
