-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_TwExtend_pw_rel
-- name    : GlobalTheory.AbLaw.TwExtend.pw_rel
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:02:02.933875+00:00
-- url     : https://prove2.me/theorems/45b6575a-c02d-4fa4-ba4d-f87d3265900d
-- title:
--   Tw Extend: pw rel
-- statement:
--   The Tw Extend construction uses the pw rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsTwExtendPowMul.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsTwExtendPowMul.lean#L67-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsTwExtendPowMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.TwExtend
variable {Y : Scheme.{0}}

theorem GlobalTheory.AbLaw.TwExtend.pw_rel {H : LB Y} {d : ℤ} (σ : LB.Sec (pw H d)) (u : ∀ l, Γ(Y, H.U l))
    (hu : ∀ l, u l = σ.f l) (l m : H.ι) {O : Y.Opens}
    (hl : O ≤ H.U l) (hm : O ≤ H.U m) (h : O ≤ H.U l ⊓ H.U m) :
    rs Y hl (u l) = (res h (H.g l m) ^ d).val * rs Y hm (u m) := by sorry
