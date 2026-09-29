-- Prove2me | Theorems.Thm_GaloisRep_isTotallyComplex_of_fixingSubgroup_le_ker_of_det_eq_modThreeCyclotomicChar
-- name    : GaloisRep.isTotallyComplex_of_fixingSubgroup_le_ker_of_det_eq_modThreeCyclotomicChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/855e5944-e946-5360-b0a2-80f6bd16c306
-- title:
--   Cyclotomic determinant forces the kernel field to be totally complex
-- statement:
--   Let $\rho$ be a group homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, to the general linear group $\mathrm{GL}_2(\mathbb{Z}/3)$, and let $F$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$ and Galois over $\mathbb{Q}$. Assume first that the fixing subgroup of $F$, i.e. the subgroup of automorphisms of $\overline{\mathbb{Q}}$ acting trivially on $F$, is contained in the kernel of $\rho$; and assume second that the composite of $\rho$ with the determinant homomorphism $\mathrm{GL}_2(\mathbb{Z}/3) \to (\mathbb{Z}/3)^\times$ equals [`WeierstrassCurve.modThreeCyclotomicChar`](def/GaloisRep_ModThreeCyclotomic.html#L10), the character sending $\sigma$ to the value at $\sigma$ (viewed as a ring automorphism of $\overline{\mathbb{Q}}$) of the modular cyclotomic character of order $3$ of $\overline{\mathbb{Q}}$, formed using the fact that an algebraically closed field of characteristic zero has exactly $3$ cube roots of unity. The conclusion is that $F$, as a number field, is totally complex: every infinite place of $F$ is complex.
--
--   This is the parity statement that an odd two-dimensional mod-$3$ representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ has totally complex splitting field, the oddness being encoded in the determinant being the mod-$3$ cyclotomic character. It feeds the discriminant-bound argument used to rule out irreducible everywhere-unramified mod-$3$ representations, being cited by [`GaloisRep.not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar`](thm.html#GaloisRep.not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_isTotallyComplex_of_fixingSubgroup_le_ker_of_det_eq_modThreeCyclotomicChar.lean

import Mathlib
import Definitions.Def_GaloisRep_ModThreeCyclotomic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.isTotallyComplex_of_fixingSubgroup_le_ker_of_det_eq_modThreeCyclotomicChar
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (hfix : F.fixingSubgroup ≤ ρ.ker)
    (hdet : Matrix.GeneralLinearGroup.det.comp ρ = WeierstrassCurve.modThreeCyclotomicChar) :
    NumberField.IsTotallyComplex F := by sorry
