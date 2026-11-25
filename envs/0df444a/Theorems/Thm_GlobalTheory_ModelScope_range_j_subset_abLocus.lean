-- Prove2me | Theorems.Thm_GlobalTheory_ModelScope_range_j_subset_abLocus
-- name    : GlobalTheory.ModelScope.range_j_subset_abLocus
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:37.515875+00:00
-- url     : https://prove2.me/theorems/cf0070de-3835-42cc-b875-2e1f5d3f428d
-- title:
--   Model Scope: range j subset ab Locus
-- statement:
--   The Model Scope construction uses the range j subset ab Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/RangeJSubsetAbLocus.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/RangeJSubsetAbLocus.lean#L23-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_RangeJSubsetAbLocus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ModelScope
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem GlobalTheory.ModelScope.range_j_subset_abLocus (Y : Model Xo c β) : Set.range Y.j ⊆ abLocus Y.t.G := by sorry
