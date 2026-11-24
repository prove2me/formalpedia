-- Prove2me | Theorems.Thm_GlobalTheory_WeilIsogeny_exists_gen_move_pow
-- name    : GlobalTheory.WeilIsogeny.exists_gen_move_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:42.093209+00:00
-- url     : https://prove2.me/theorems/cc91543e-bc1f-4063-ba81-fa1ea72db97a
-- title:
--   Weil Isogeny: exists gen move pow
-- statement:
--   The Weil Isogeny construction uses the exists gen move pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenMovePow.lean#L55-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenMovePow.lean#L55-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenMovePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilIsogeny
open CommutatorPairing
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}

theorem GlobalTheory.WeilIsogeny.exists_gen_move_pow {X₀ Y₀ : Scheme.{0}} {M : LB X₀} {F : X ⟶ X₀} (hL : L.IsLB) (hM : M.IsLB) {d : ℕ}
    (w : LB.Iso (lbPow L d) (M.pull F)) (hw : w.IsGen) (hε : ∀ k, ε' k = ε k * d) {φ₀ : K → (Y₀ ⟶ X₀)} (h : Y ⟶ Y₀)
    (hc : ∀ k, φ k ≫ F = h ≫ φ₀ k) (t : LB.Gen (LB.LinComb M φ₀ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J₀),
      Good L z J → Good M z J₀ → val t (r ≫ h) z J₀ =
        (∏ k, (fun χ : Z ⟶ X => gw w χ z (J₀ (χ ≫ F)) (fun _ => J χ)) (r ≫ φ k) ^ ε k) * val u r z J := by sorry
