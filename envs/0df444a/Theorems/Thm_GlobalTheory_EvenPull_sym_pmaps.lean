-- Prove2me | Theorems.Thm_GlobalTheory_EvenPull_sym_pmaps
-- name    : GlobalTheory.EvenPull.sym_pmaps
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:07:44.996042+00:00
-- url     : https://prove2.me/theorems/eb8f1daa-f088-46b8-be4f-354985a9a194
-- title:
--   Even Pull: sym pmaps
-- statement:
--   The Even Pull construction uses the sym pmaps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PulledComparisonEven.lean#L70-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PulledComparisonEven.lean#L70-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PulledComparisonEven
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EvenPull

theorem GlobalTheory.EvenPull.sym_pmaps (hG : GlobalFnsSt) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    PMaps hD.w (K := Fin 2) ![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] ![(ι[D.P.A]).left, 𝟙 D.P.A.left] ![1, -1]
      D'.sym D.sym (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by sorry
