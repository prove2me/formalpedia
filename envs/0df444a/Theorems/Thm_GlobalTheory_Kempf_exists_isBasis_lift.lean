-- Prove2me | Theorems.Thm_GlobalTheory_Kempf_exists_isBasis_lift
-- name    : GlobalTheory.Kempf.exists_isBasis_lift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:47:34.916615+00:00
-- url     : https://prove2.me/theorems/07a1f90f-252c-48ec-aa32-57d2725052ea
-- title:
--   Kempf: exists is Basis lift
-- statement:
--   The Kempf construction uses the exists is Basis lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L142-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L142-L154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Opposite TopologicalSpace
universe w u v' u'
noncomputable section
open GlobalTheory
open GlobalTheory.Kempf
variable {X : TopCat.{u}}
variable {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}

theorem GlobalTheory.Kempf.exists_isBasis_lift (hS : S.ShortExact) {𝔅 : Set (Opens X)} (h𝔅 : Opens.IsBasis 𝔅)
    {V : Opens X} (s : S.X₃.obj.obj (op V)) {x : X} (hx : x ∈ V) :
    ∃ W ∈ 𝔅, x ∈ W ∧ W ≤ V ∧ ∃ t : S.X₂.obj.obj (op (V ⊓ W)),
      S.g.hom.app (op (V ⊓ W)) t = S.X₃.obj.map (homOfLE inf_le_left).op s := by sorry
