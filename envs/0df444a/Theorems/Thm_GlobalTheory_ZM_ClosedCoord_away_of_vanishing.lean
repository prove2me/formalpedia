-- Prove2me | Theorems.Thm_GlobalTheory_ZM_ClosedCoord_away_of_vanishing
-- name    : GlobalTheory.ZM.ClosedCoord.away_of_vanishing
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:49:17.973892+00:00
-- url     : https://prove2.me/theorems/beef7ba9-2d77-4640-a713-27a5dce2003c
-- title:
--   Closed Coord: away of vanishing
-- statement:
--   The Closed Coord construction uses the away of vanishing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsProjectiveCoordinateRepresentationClosedSubsch.lean#L79-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsProjectiveCoordinateRepresentationClosedSubsch.lean#L79-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProjectiveCoordinateRepresentationClosedSubsch
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.ClosedCoord
open MvPolynomial

theorem GlobalTheory.ZM.ClosedCoord.away_of_vanishing {R σ : Type} [CommRing R] [Finite σ]
    (P : ∀ (R' : Type) [CommRing R'], (R →+* R') → (σ → R') → Prop)
    (bc : ∀ (R' R'' : Type) [CommRing R'] [CommRing R''] (φ : R' →+* R'') β v, P R' β v → P R'' (φ.comp β) (fun j => φ (v j)))
    (sc : ∀ (R' : Type) [CommRing R'] (u : R'ˣ) β v, P R' β v → P R' β (fun j => u * v j))
    (uni : ∀ (R' : Type) [CommRing R'] β v, P R' β v → Ideal.span (Set.range v) = ⊤)
    (ch : ∀ a, ∃ K : Ideal (MvPolynomial σ R), X a - 1 ∈ K ∧ ∀ (R' : Type) [CommRing R'] β w, w a = 1 →
      (P R' β w ↔ ∀ F ∈ K, eval₂ β w F = 0))
    (R' : Type) [CommRing R'] (β : R →+* R') (v : σ → R')
    (hv : ∀ F, (∀ (R'' : Type) [CommRing R''] β' w, P R'' β' w → eval₂ β' w F = 0) → eval₂ β v F = 0) (a : σ) :
    P (Localization.Away (v a)) ((algebraMap R' _).comp β) (fun j => algebraMap R' _ (v j)) := by sorry
