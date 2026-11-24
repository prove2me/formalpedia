-- Prove2me | Theorems.Thm_GlobalTheory_firstJet_eq_prod_tangent
-- name    : GlobalTheory.firstJet_eq_prod_tangent
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:06:12.996797+00:00
-- url     : https://prove2.me/theorems/eeeec16b-50ba-447c-9433-1ad68f5ea37d
-- title:
--   Global Theory: first Jet eq prod tangent
-- statement:
--   The Global Theory construction uses the first Jet eq prod tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FirstJetEqProdTangent.lean#L40-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FirstJetEqProdTangent.lean#L40-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstJetEqProdTangent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open SqZero TrivSqZeroExt

theorem GlobalTheory.firstJet_eq_prod_tangent : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)),
    IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G),
    (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) →
    (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) →
    ∀ (A : Type) [CommRing A] [Algebra R A] (ψ : JetR R (Fin d) 1 →ₐ[R] A)
      (e : Fin d → (DualNumber R →ₐ[R] A)), (∀ j, e j (TrivSqZeroExt.inr 1) = ψ (zR 1 j)) →
      spMap ψ ≫ x 1 = ∏ j, (spMap (e j) ≫ v j : sp (R₀ := R) A ⟶ G) := by sorry
