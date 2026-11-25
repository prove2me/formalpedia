-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_eventually_forall_placesOver
-- name    : GroundTheory.Global.IdeleNorm.eventually_forall_placesOver
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:51:37.522015+00:00
-- url     : https://prove2.me/theorems/32d5c200-fd73-484c-9a3c-eb96068d2e36
-- title:
--   Idele Norm: eventually forall places Over
-- statement:
--   The Idele Norm construction uses the eventually forall places Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L95-L102

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]
variable {L}
omit [NumberField K] [NumberField L]
variable (K)

theorem GroundTheory.Global.IdeleNorm.eventually_forall_placesOver {P : HeightOneSpectrum (𝓞 L) → Prop}
    (h : ∀ᶠ w in cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ w : PlacesOver L v, P w.1 := by sorry
