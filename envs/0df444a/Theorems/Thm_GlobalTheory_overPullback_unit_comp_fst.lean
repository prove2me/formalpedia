-- Prove2me | Theorems.Thm_GlobalTheory_overPullback_unit_comp_fst
-- name    : GlobalTheory.overPullback_unit_comp_fst
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:01.38798+00:00
-- url     : https://prove2.me/theorems/4dd3c2bb-ffd1-4e2a-86a2-adb463e6d798
-- title:
--   Global Theory: over Pullback unit comp fst
-- statement:
--   The Global Theory construction uses the over Pullback unit comp fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemUnitComponentMulMem.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemUnitComponentMulMem.lean#L9-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMemRightTranslateMemIdentityComponentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemUnitComponentMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.overPullback_unit_comp_fst {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    (η[(Over.pullback p).obj G]).left ≫ pullback.fst G.hom p = p ≫ (η[G]).left := by sorry
