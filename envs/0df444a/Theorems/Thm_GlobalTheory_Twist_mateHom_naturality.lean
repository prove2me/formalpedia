-- Prove2me | Theorems.Thm_GlobalTheory_Twist_mateHom_naturality
-- name    : GlobalTheory.Twist.mateHom_naturality
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:20:28.114022+00:00
-- url     : https://prove2.me/theorems/9517dc05-2ccd-4f99-a217-8880f5f09fc4
-- title:
--   Twist: mate Hom naturality
-- statement:
--   The Twist construction uses the mate Hom naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasicoherentOfLocallyIso.lean#L235-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasicoherentOfLocallyIso.lean#L235-L243

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
variable {C D : Type*} [Category C] [Category D] {P : C ⥤ D} {Q : D ⥤ C} (adj : P ⊣ Q)
  (S : C ⥤ C) (T : D ⥤ D) (e : Q ⋙ S ≅ T ⋙ Q)

theorem GlobalTheory.Twist.mateHom_naturality {A B : C} (f : A ⟶ B) :
    P.map (S.map f) ≫ mateHom adj S T e B = mateHom adj S T e A ≫ T.map (P.map f) := by sorry
