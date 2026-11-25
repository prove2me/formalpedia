-- Prove2me | Theorems.Thm_GlobalTheory_ZV_FormSec_ideal_of_veryAmple
-- name    : GlobalTheory.ZV.FormSec.ideal_of_veryAmple
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:02:42.535797+00:00
-- url     : https://prove2.me/theorems/abf92278-297a-59cb-8b64-626c237f054c
-- title:
--   Form Sec: ideal of very Ample
-- statement:
--   The Form Sec construction uses the ideal of very Ample property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HomogeneousIdealSectionsOfLineBundlePower.lean#L187-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HomogeneousIdealSectionsOfLineBundlePower.lean#L187-L190

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
import Theorems.Thm_GlobalTheory_ZV_ActsBy_comp
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
open GlobalTheory.ZV
noncomputable section
open GlobalTheory GlobalTheory.ZV GlobalTheory.ZV.FormSec
open GlobalTheory.SegreCoord (ev ev_eq ev_ext ev_stalkMap Loc loc_of_secCoord exists_secCoord)
variable {R σ : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ Sp R} {M : LB X} {th : σ → M.Sec}

theorem GlobalTheory.ZV.FormSec.ideal_of_veryAmple : ∀ (K σ : Type) [Field K] [Finite σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → (∀ F ∈ idealOf p M th (𝟙 X), ∀ e, MvPolynomial.homogeneousComponent e F ∈ idealOf p M th (𝟙 X)) ∧ (∀ F, (∀ i, MvPolynomial.X i * F ∈ idealOf p M th (𝟙 X)) → F ∈ idealOf p M th (𝟙 X)) ∧ ∀ (d : ℕ) (F : MvPolynomial σ K), F.IsHomogeneous d → ∃ τ : (lbPow M d).Sec, (∀ j, τ.f j = MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F) ∧ ((∀ j, τ.f j = 0) ↔ F ∈ idealOf p M th (𝟙 X)) ∧ ∀ (y : Sp K ⟶ X) (v : σ → K), y ≫ p = 𝟙 _ → SecCoord M th y v → (MvPolynomial.eval v F = 0 ↔ ¬ ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus τ) := by sorry
