-- Prove2me | Theorems.Thm_GlobalTheory_ChartBaseChange_exists_pt_of_aug
-- name    : GlobalTheory.ChartBaseChange.exists_pt_of_aug
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:49.988801+00:00
-- url     : https://prove2.me/theorems/bfc43607-2145-4ed4-b2ce-4a98b497d432
-- title:
--   Chart Base Change: exists pt of aug
-- statement:
--   The Chart Base Change construction uses the exists pt of aug property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L138-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L138-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom)
open GlobalTheory.JetSer ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem GlobalTheory.ChartBaseChange.exists_pt_of_aug (C : Chart G) {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (q : A →ₐ[R] B) (hq : Function.Surjective q) {m : ℕ} (hJ : (RingHom.ker q) ^ (m + 1) = ⊥)
    (y : sp (R₀ := R) A ⟶ G) (hy : spMap q ≫ y = 1) :
    ∃ h : Γ(G.left, C.U) →ₐ[R] A, y = ReciprocityTheory.ChartRestriction.G.Chart.pt C h ∧ q.comp h = (Algebra.ofId R B).comp (eps C) := by sorry
