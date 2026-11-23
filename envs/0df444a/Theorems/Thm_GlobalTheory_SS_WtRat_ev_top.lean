-- Prove2me | Theorems.Thm_GlobalTheory_SS_WtRat_ev_top
-- name    : GlobalTheory.SS.WtRat.ev_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:41.467779+00:00
-- url     : https://prove2.me/theorems/fd410f50-0c2a-4f60-9ea3-39f6c9bf6499
-- title:
--   Wt Rat: ev top
-- statement:
--   The Wt Rat construction uses the ev top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsUnitEv.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsUnitEv.lean#L54-L59

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

theorem GlobalTheory.SS.WtRat.ev_top (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) (u : Γ(Y, ⊤)) :
    _root_.GlobalTheory.SS.WtRat.ev g ⊤ h u =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (g.appTop.hom u) := by sorry
