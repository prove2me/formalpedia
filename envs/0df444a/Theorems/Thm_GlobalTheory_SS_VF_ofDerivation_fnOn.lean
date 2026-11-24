-- Prove2me | Theorems.Thm_GlobalTheory_SS_VF_ofDerivation_fnOn
-- name    : GlobalTheory.SS.VF.ofDerivation_fnOn
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:37:58.495666+00:00
-- url     : https://prove2.me/theorems/e17d8421-ed53-4f34-9e78-352b06a7f2f8
-- title:
--   VF: of Derivation fn On
-- statement:
--   The VF construction uses the of Derivation fn On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/OfDerivationFnOn.lean#L294-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/OfDerivationFnOn.lean#L294-L295

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SS
variable (R : Type) [CommRing R] {K : Type} [Field K] [Algebra R K]
variable {R} {A A' : Over (Sp K)}
variable {B : Type} [CommRing B] [Algebra K B]

theorem GlobalTheory.SS.VF.ofDerivation_fnOn (d : Derivation K B B) (U : (Sp B).Opens) (b : B) :
    (VF.ofDerivation d).D U (fnOn B U b) = fnOn B U (d b) := by sorry
