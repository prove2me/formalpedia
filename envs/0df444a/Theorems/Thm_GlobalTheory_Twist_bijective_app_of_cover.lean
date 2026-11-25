-- Prove2me | Theorems.Thm_GlobalTheory_Twist_bijective_app_of_cover
-- name    : GlobalTheory.Twist.bijective_app_of_cover
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:51.412851+00:00
-- url     : https://prove2.me/theorems/7155f442-2502-59b5-b71a-59d265f67444
-- title:
--   Twist: bijective app of cover
-- statement:
--   The Twist construction uses the bijective app of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasicoherentOfLocallyIso.lean#L52-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasicoherentOfLocallyIso.lean#L52-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res le_iSup_inf unitMod homOfLinear isoOfLinear toMod)
open GlobalTheory
open GlobalTheory.Twist
variable {X Y : Scheme.{0}}
variable {F G : X.Modules}

theorem GlobalTheory.Twist.bijective_app_of_cover (φ : F ⟶ G) {ι : Type*} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    (V : X.Opens) (h : ∀ (k : ι) (W : X.Opens), W ≤ V → W ≤ U k → Function.Bijective (φ.app W)) :
    Function.Bijective (φ.app V) := by sorry
