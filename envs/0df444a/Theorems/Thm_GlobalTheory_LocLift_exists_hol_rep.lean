-- Prove2me | Theorems.Thm_GlobalTheory_LocLift_exists_hol_rep
-- name    : GlobalTheory.LocLift.exists_hol_rep
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:46:13.235809+00:00
-- url     : https://prove2.me/theorems/54604b38-6495-4809-80b6-73ef009c0827
-- title:
--   Loc Lift: exists hol rep
-- statement:
--   The Loc Lift construction uses the exists hol rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHolLinearLift.lean#L57-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHolLinearLift.lean#L57-L84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
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
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}

theorem GlobalTheory.LocLift.exists_hol_rep {O : Type} [CommRing O] {B : Set (Fin m → ℂ)} (hB : IsOpen B) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B)
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {r : ℝ} (hr : 0 < r)
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : ∀ b ∈ B, IsExp (y b) (e b) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) (hl : HasLifts B y e)
    (act : OAct O G) :
    ∃ F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ),
      (∀ b ∈ B, ∀ a z, e b ((F b a).mulVec z) = e b z ≫ act.act a) ∧
      ∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B := by sorry
