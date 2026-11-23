-- Prove2me | Theorems.Thm_GlobalTheory_SS_WtRat_ev_spMap
-- name    : GlobalTheory.SS.WtRat.ev_spMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:42.368458+00:00
-- url     : https://prove2.me/theorems/ee00f0f3-d021-4485-b9ed-a2e033ad9e6a
-- title:
--   Wt Rat: ev sp Map
-- statement:
--   The Wt Rat construction uses the ev sp Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsUnitEv.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsUnitEv.lean#L65-L72

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

theorem GlobalTheory.SS.WtRat.ev_spMap (σ : R →+* R') (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (h' : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ ≫ g) ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ ≫ g) V h' u =
      σ (_root_.GlobalTheory.SS.WtRat.ev g V h u) := by sorry
