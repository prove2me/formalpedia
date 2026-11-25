-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_placesOver_congr
-- name    : GroundTheory.Global.IdeleNorm.placesOver_congr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:36.534803+00:00
-- url     : https://prove2.me/theorems/30504ffa-b9a8-50e4-8b1f-7cb5c76d431c
-- title:
--   Idele Norm: places Over congr
-- statement:
--   The Idele Norm construction uses the places Over congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L106-L112

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
omit [NumberField K]

theorem GroundTheory.Global.IdeleNorm.placesOver_congr (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    {v v' : HeightOneSpectrum (𝓞 K)} (h : v' = v) (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal) (hw' : w.asIdeal.LiesOver v'.asIdeal) :
    yf v' ⟨w, hw'⟩ = yf v ⟨w, hw⟩ := by sorry
