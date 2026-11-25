-- Prove2me | Theorems.Thm_GlobalTheory_ChartUniv_isUnivChart_ren
-- name    : GlobalTheory.ChartUniv.isUnivChart_ren
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:11:03.743634+00:00
-- url     : https://prove2.me/theorems/77b4928e-52f1-42f3-8b0b-ebaadc5fa7ec
-- title:
--   Chart Univ: is Univ Chart ren
-- statement:
--   The Chart Univ construction uses the is Univ Chart ren property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsUniversalChartOfFormalGroupChart.lean#L78-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsUniversalChartOfFormalGroupChart.lean#L78-L114

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartUniv
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem GlobalTheory.ChartUniv.isUnivChart_ren [IsLocalRing R] [Smooth G.hom] {κ : Type} {d : ℕ} (e : κ ≃ Fin d)
    (x : ∀ m, sp (R₀ := R) (JetR R κ m) ⟶ G)
    (ht : ∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m)
    (h0 : ∀ m, spMap (jetZeroR R κ m) ≫ x m = 1)
    (hu : ∀ (κ' : Type) (m : ℕ) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x m) :
    IsUnivChart G d (fun m => spMap (jetRen e m) ≫ x m) := by sorry
