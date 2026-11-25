-- Prove2me | Theorems.Thm_GlobalTheory_ZV_FormSec_mem_idealOf
-- name    : GlobalTheory.ZV.FormSec.mem_idealOf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:47:49.268055+00:00
-- url     : https://prove2.me/theorems/9e9e4a89-73d1-4071-84b0-f3e0a2cd5c78
-- title:
--   Form Sec: mem ideal Of
-- statement:
--   The Form Sec construction uses the mem ideal Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HomogeneousIdealSectionsOfLineBundlePower.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HomogeneousIdealSectionsOfLineBundlePower.lean#L34-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HomogeneousIdealSectionsOfLineBundlePower
import Theorems.Thm_GlobalTheory_SegreCoord_ev_eq
import Theorems.Thm_GlobalTheory_SegreCoord_ev_ext
import Theorems.Thm_GlobalTheory_SegreCoord_ev_stalkMap
import Theorems.Thm_GlobalTheory_SegreCoord_exists_secCoord
import Theorems.Thm_GlobalTheory_SegreCoord_loc_of_secCoord

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
open GlobalTheory.ZV
noncomputable section
open GlobalTheory GlobalTheory.ZV GlobalTheory.ZV.FormSec
open GlobalTheory.SegreCoord (ev ev_eq ev_ext ev_stalkMap Loc loc_of_secCoord exists_secCoord)
variable {R σ : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ Sp R} {M : LB X} {th : σ → M.Sec}

theorem GlobalTheory.ZV.FormSec.mem_idealOf {F : MvPolynomial σ R} : F ∈ idealOf p M th (𝟙 X) ↔
    ∀ (T : Type) [CommRing T] (β : R →+* T) (y : Sp T ⟶ X) (v : σ → T), y ≫ p = spMap β → SecCoord M th y v →
      MvPolynomial.eval₂ β v F = 0 := by sorry
