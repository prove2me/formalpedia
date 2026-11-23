-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_HermClass_exists_zero_coord_ne_zero
-- name    : GlobalTheory.LocalQuad.HermClass.exists_zero_coord_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:53.332631+00:00
-- url     : https://prove2.me/theorems/194944b6-74b4-4e90-bd74-b3bc0753005e
-- title:
--   Herm Class: exists zero coord ne zero
-- statement:
--   The Herm Class construction uses the exists zero coord ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroCoordNeZero.lean#L86-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroCoordNeZero.lean#L86-L119

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.HermClass

theorem GlobalTheory.LocalQuad.HermClass.exists_zero_coord_ne_zero {F : Type*} [Field F] [CharZero F] {ι : Type*} [Fintype ι]
    {a : ι → F} (ha : ∀ i, a i ≠ 0) {z : ι → F} (hz : z ≠ 0) (h : ∑ i, a i * z i ^ 2 = 0)
    (i : ι) : ∃ w : ι → F, w i ≠ 0 ∧ ∑ k, a k * w k ^ 2 = 0 := by sorry
