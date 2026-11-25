-- Prove2me | Theorems.Thm_GlobalTheory_Twist_isFiniteType_of_locally_iso
-- name    : GlobalTheory.Twist.isFiniteType_of_locally_iso
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:04.746356+00:00
-- url     : https://prove2.me/theorems/a7901b24-3ee9-45b7-8c77-483824394ea1
-- title:
--   Twist: is Finite Type of locally iso
-- statement:
--   The Twist construction uses the is Finite Type of locally iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasicoherentOfLocallyIso.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasicoherentOfLocallyIso.lean#L134-L138

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
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.Twist.isFiniteType_of_locally_iso {ι : Type} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    (e : ∀ (k : ι) (W : X.Opens), W ≤ U k → (F.restrict W.ι ≅ G.restrict W.ι))
    [hF : F.IsFiniteType] : G.IsFiniteType := by sorry
