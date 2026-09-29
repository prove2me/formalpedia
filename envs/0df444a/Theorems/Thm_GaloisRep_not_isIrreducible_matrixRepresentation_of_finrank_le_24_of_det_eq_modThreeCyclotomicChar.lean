-- Prove2me | Theorems.Thm_GaloisRep_not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar
-- name    : GaloisRep.not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/ffa37fc6-fca3-5b5f-8eeb-bac7b22758c1
-- title:
--   Reducibility of small mod-3 representations unramified outside 3
-- statement:
--   Let $\rho$ be a group homomorphism from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}}) = \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, for $\overline{\mathbb{Q}}$ the algebraic closure of $\mathbb{Q}$ constructed in Mathlib, to $\mathrm{GL}_2(\mathbb{Z}/3)$, and let $F$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional and Galois over $\mathbb{Q}$. Assume: the subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing $F$ pointwise is exactly $\ker\rho$; $[F:\mathbb{Q}] \le 24$; every maximal ideal $P$ of the ring of integers of $F$ with $3 \notin P$ is unramified over $\mathbb{Z}$, in the sense of `Algebra.IsUnramifiedAt`; and the composite of $\rho$ with the determinant $\mathrm{GL}_2(\mathbb{Z}/3) \to (\mathbb{Z}/3)^{\times}$ equals [`WeierstrassCurve.modThreeCyclotomicChar`](def/GaloisRep_ModThreeCyclotomic.html#L10), the character $\sigma \mapsto \chi_3(\sigma)$ given by the action of $\sigma$ on the cube roots of unity of $\overline{\mathbb{Q}}$ via `modularCyclotomicCharacter`. The conclusion is that the associated linear representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $(\mathbb{Z}/3)^2$, namely [`Deformation.matrixRepresentation ρ`](def/Deformations_MatrixRepresentation.html#L15) obtained by composing $\rho$ with the identification of invertible matrices with invertible linear maps, is not irreducible.
--
--   This is the small-image branch of Serre's exclusion of irreducible two-dimensional mod-$3$ representations of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of level one: an image of order at most $24$ with cyclotomic determinant whose kernel field is unramified outside $3$ cannot act irreducibly. The argument combines a count of subgroups of $\mathrm{GL}_2(\mathbb{F}_3)$ with surjective determinant and no common eigenline, whose order then divides $16$, with the fact that a Galois extension of $\mathbb{Q}$ of $2$-power degree dividing $16$ and unramified outside $3$ has degree at most $2$; it feeds the version [`GaloisRep.not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar`](thm.html#GaloisRep.not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar.lean

import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_GaloisRep_ModThreeCyclotomic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (hfix : F.fixingSubgroup = ρ.ker)
    (h24 : Module.finrank ℚ F ≤ 24)
    (hunr : ∀ (P : Ideal (NumberField.RingOfIntegers F)) [P.IsMaximal],
      (3 : NumberField.RingOfIntegers F) ∉ P → Algebra.IsUnramifiedAt ℤ P)
    (hdet : Matrix.GeneralLinearGroup.det.comp ρ = WeierstrassCurve.modThreeCyclotomicChar) :
    ¬ Representation.IsIrreducible (Deformation.matrixRepresentation ρ) := by sorry
