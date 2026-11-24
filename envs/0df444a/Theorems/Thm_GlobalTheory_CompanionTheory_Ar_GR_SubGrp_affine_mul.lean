-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_affine_mul
-- name    : GlobalTheory.CompanionTheory.Ar.GR.SubGrp.affine_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:19:21.66389+00:00
-- url     : https://prove2.me/theorems/2c8f7c90-858e-477a-a99e-7c6f852caaf8
-- title:
--   Sub Grp: affine mul
-- statement:
--   The Sub Grp construction uses the affine mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFlatSubgroupScheme.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFlatSubgroupScheme.lean#L118-L126

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.GR GlobalTheory.CompanionTheory.Ar.GR.SubGrp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
variable {R : Type} [CommRing R]
variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]
  {h : sp (R₀ := R) B ⟶ A}

theorem GlobalTheory.CompanionTheory.Ar.GR.SubGrp.affine_mul (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a b : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = (a ≫ h) * (b ≫ h) := by sorry
