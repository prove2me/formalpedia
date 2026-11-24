-- Prove2me | Theorems.Thm_GlobalTheory_Kempf_exists_mem_map_toInter_eq_zero
-- name    : GlobalTheory.Kempf.exists_mem_map_toInter_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:48:43.610992+00:00
-- url     : https://prove2.me/theorems/1d2f42bc-e8d8-4820-83ca-0953a0d690d1
-- title:
--   Kempf: exists mem map to Inter eq zero
-- statement:
--   The Kempf construction uses the exists mem map to Inter eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L194-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsIsoToInterAppPushforwardInclusion.lean#L194-L223

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
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
open SheafLES

theorem GlobalTheory.Kempf.exists_mem_map_toInter_eq_zero {𝔅 : Set (Opens X)} (h𝔅 : Opens.IsBasis 𝔅)
    (hinf : ∀ B ∈ 𝔅, ∀ B' ∈ 𝔅, B ⊓ B' ∈ 𝔅) (V : Opens X) (n : ℕ)
    (F : X.Sheaf AddCommGrpCat.{u})
    (hF : ∀ q, 0 < q → q < n + 1 → ∀ B ∈ 𝔅, Subsingleton (Sheaf.H'.{w} F q B))
    (α : Sheaf.H'.{w} F (n + 1) V) {x : X} (hx : x ∈ V) :
    ∃ W ∈ 𝔅, x ∈ W ∧ W ≤ V ∧
      map.{w} ((toInter AddCommGrpCat.{u} W).app F) (n + 1) V α = 0 := by sorry
