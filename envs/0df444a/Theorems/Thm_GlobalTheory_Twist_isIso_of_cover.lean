-- Prove2me | Theorems.Thm_GlobalTheory_Twist_isIso_of_cover
-- name    : GlobalTheory.Twist.isIso_of_cover
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:13:34.481327+00:00
-- url     : https://prove2.me/theorems/6cdb22af-329d-53fb-8270-32e3d22c2881
-- title:
--   Twist: is Iso of cover
-- statement:
--   The Twist construction uses the is Iso of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasicoherentOfLocallyIso.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasicoherentOfLocallyIso.lean#L75-L77

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

theorem GlobalTheory.Twist.isIso_of_cover (φ : F ⟶ G) {ι : Type*} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    (h : ∀ (k : ι) (W : X.Opens), W ≤ U k → Function.Bijective (φ.app W)) : IsIso φ := by sorry
