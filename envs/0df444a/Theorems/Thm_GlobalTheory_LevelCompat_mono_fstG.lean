-- Prove2me | Theorems.Thm_GlobalTheory_LevelCompat_mono_fstG
-- name    : GlobalTheory.LevelCompat.mono_fstG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:33.736634+00:00
-- url     : https://prove2.me/theorems/de03a1bf-4c64-489b-b7af-fad7abbd43f0
-- title:
--   Level Compat: mono fst G
-- statement:
--   The Level Compat construction uses the mono fst G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GtCoordCompatOfPull.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GtCoordCompatOfPull.lean#L23-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GtCoordCompatOfPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.LevelCompat
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.LevelCompat.mono_fstG {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) : Mono (fstG I e G).left := by sorry
