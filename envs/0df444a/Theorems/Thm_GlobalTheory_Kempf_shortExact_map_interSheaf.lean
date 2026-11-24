-- Prove2me | Theorems.Thm_GlobalTheory_Kempf_shortExact_map_interSheaf
-- name    : GlobalTheory.Kempf.shortExact_map_interSheaf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:48:31.913569+00:00
-- url     : https://prove2.me/theorems/b45423be-4120-44e0-b6c1-fd9f81afc295
-- title:
--   Kempf: short Exact map inter Sheaf
-- statement:
--   The Kempf construction uses the short Exact map inter Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L132-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L132-L140

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

theorem GlobalTheory.Kempf.shortExact_map_interSheaf (hS : S.ShortExact) {𝔅 : Set (Opens X)} (h𝔅 : Opens.IsBasis 𝔅)
    (hinf : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ⊓ B' ∈ 𝔅)
    (hsurj : ∀ B ∈ 𝔅, Function.Surjective (S.g.hom.app (op B))) {W : Opens X} (hW : W ∈ 𝔅) :
    (S.map (interSheaf AddCommGrpCat.{u} W)).ShortExact := by sorry
