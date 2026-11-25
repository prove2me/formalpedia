-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenModelSections_Model_incl_mem_abLocus
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.Model.incl_mem_abLocus
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:46.25881+00:00
-- url     : https://prove2.me/theorems/7cf3f213-947d-4554-8e5d-21452e51850e
-- title:
--   Model: incl mem ab Locus
-- statement:
--   The Model construction uses the incl mem ab Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/OpenModelSections.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/OpenModelSections.lean#L120-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoefficientFieldBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_OpenModelSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
open GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.Model
variable {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
  {univ : Obj D l (baseKA l) str} {F₀ : IntermediateField ℚ ℂ} {h : IsCoeffField l F₀}
  {O : Type} [CommRing O] {φ : O →+* F₀} (m : Model univ h φ)

theorem GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.Model.incl_mem_abLocus (y : ↥(baseChange str h)) : m.incl y ∈ abLocus m.t.G := by sorry
