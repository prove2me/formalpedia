-- Prove2me | Theorems.Thm_GlobalTheory_Kempf_exact_map_interSheaf
-- name    : GlobalTheory.Kempf.exact_map_interSheaf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:59.505001+00:00
-- url     : https://prove2.me/theorems/3e33545d-3f4b-4559-8c26-9a6864c65c79
-- title:
--   Kempf: exact map inter Sheaf
-- statement:
--   The Kempf construction uses the exact map inter Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L126-L130

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

theorem GlobalTheory.Kempf.exact_map_interSheaf (hS : S.ShortExact) (W : Opens X) :
    (S.map (interSheaf AddCommGrpCat.{u} W)).Exact ∧
      Mono (S.map (interSheaf AddCommGrpCat.{u} W)).f := by sorry
