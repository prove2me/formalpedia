-- Prove2me | Theorems.Thm_GlobalTheory_InnerRead_sub_prF_mem
-- name    : GlobalTheory.InnerRead.sub_prF_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:39:42.573888+00:00
-- url     : https://prove2.me/theorems/0de4a13b-90ec-4d9e-bc5b-aa6fc8ac1415
-- title:
--   Inner Read: sub pr F mem
-- statement:
--   The Inner Read construction uses the sub pr F mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NonGenericDatumLatticeEqPerpQuotientImageTerm.lean#L143-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NonGenericDatumLatticeEqPerpQuotientImageTerm.lean#L143-L149

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NonGenericDatumLatticeEqPerpQuotientImageTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
noncomputable section
open GlobalTheory GlobalTheory.InnerRead
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {H} {r : ℕ} (Fr : FrameD H r)

theorem GlobalTheory.InnerRead.sub_prF_mem (v : V) (hv : v ∈ H.perp (H.X Fr.f)) : v - Fr.prF v ∈ H.X Fr.f := by sorry
