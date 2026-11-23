-- Prove2me | Theorems.Thm_GlobalTheory_SS_WtRat_ev_res
-- name    : GlobalTheory.SS.WtRat.ev_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:43.776023+00:00
-- url     : https://prove2.me/theorems/c614add5-827a-4acb-ad1e-d31add83f958
-- title:
--   Wt Rat: ev res
-- statement:
--   The Wt Rat construction uses the ev res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsUnitEv.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsUnitEv.lean#L43-L48

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

theorem GlobalTheory.SS.WtRat.ev_res (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) {V W : Y.Opens} (e : W ≤ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ g ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev g W h ((Y.presheaf.map (homOfLE e).op).hom u) =
      _root_.GlobalTheory.SS.WtRat.ev g V h' u := by sorry
