-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_RamifiedPlacesSplitEigen_IsDetSection_smul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen.IsDetSection.smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:36:07.529253+00:00
-- url     : https://prove2.me/theorems/80fd2ab0-87a1-45cd-a4a7-8d04603a64a8
-- title:
--   Is Det Section: smul
-- statement:
--   The Is Det Section construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/RamifiedPlacesSplitEigen.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/RamifiedPlacesSplitEigen.lean#L75-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_RamifiedPlacesSplitEigen
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen.IsDetSection.smul {Y : Model Xo c β} {τ : E →+* ℂ} {f : Rule Y} (hf : IsDetSection Y τ f) (a : c.F) :
    IsDetSection Y τ (fun R _ φ x v w => φ a * f R φ x v w) := by sorry
