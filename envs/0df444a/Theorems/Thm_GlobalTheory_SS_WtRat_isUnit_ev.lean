-- Prove2me | Theorems.Thm_GlobalTheory_SS_WtRat_isUnit_ev
-- name    : GlobalTheory.SS.WtRat.isUnit_ev
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:37:55.552909+00:00
-- url     : https://prove2.me/theorems/1d528020-210e-43cb-9a31-a6c3edeb8d06
-- title:
--   Wt Rat: is Unit ev
-- statement:
--   The Wt Rat construction uses the is Unit ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsUnitEv.lean#L90-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsUnitEv.lean#L90-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
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
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}}
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}}

theorem GlobalTheory.SS.WtRat.isUnit_ev (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (u : Γ(Y, V)) (hu : ⊤ ≤ g ⁻¹ᵁ Y.basicOpen u) :
    IsUnit (_root_.GlobalTheory.SS.WtRat.ev g V h u) := by sorry
