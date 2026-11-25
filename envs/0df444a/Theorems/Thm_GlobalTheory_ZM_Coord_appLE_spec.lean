-- Prove2me | Theorems.Thm_GlobalTheory_ZM_Coord_appLE_spec
-- name    : GlobalTheory.ZM.Coord.appLE_spec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:33:48.754876+00:00
-- url     : https://prove2.me/theorems/00020359-1d8c-45ee-8c7d-3fd294b6c613
-- title:
--   Coord: app LE spec
-- statement:
--   The Coord construction uses the app LE spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SecCoordBcScaleUnique.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SecCoordBcScaleUnique.lean#L29-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.Coord
open GlobalTheory.ZM.RepBC

theorem GlobalTheory.ZM.Coord.appLE_spec {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (e : (⊤ : (Sp R').Opens) ≤ spMap φ ⁻¹ᵁ ⊤)
    (a : R) : ((spMap φ).appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (φ a) := by sorry
