-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FibreFramesOnModels_isBaseRing_local
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.isBaseRing_local
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:35.077845+00:00
-- url     : https://prove2.me/theorems/daa416ab-aea6-4cbd-b757-d1e064edf884
-- title:
--   Fibre Frames On Models: is Base Ring local
-- statement:
--   The Fibre Frames On Models construction uses the is Base Ring local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/FibreFramesOnModels.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/FibreFramesOnModels.lean#L108-L112

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_FibreFramesOnModels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.isBaseRing_local (c : Coeff l) (W : ValuationSubring ℂ) : IsBaseRing (c.V W).subtype := by sorry
