-- Prove2me | Theorems.Thm_GlobalTheory_ChartBaseChange_hasSer_move
-- name    : GlobalTheory.ChartBaseChange.hasSer_move
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:10:15.426969+00:00
-- url     : https://prove2.me/theorems/ee85b83f-c364-45b6-a2ce-aed74fdd1f1b
-- title:
--   Chart Base Change: has Ser move
-- statement:
--   The Chart Base Change construction uses the has Ser move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L313-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L313-L326

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
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
variable {d n N : ℕ}

theorem GlobalTheory.ChartBaseChange.hasSer_move {a : Fin N → Pt R' n d} {Θ : ∀ m, JetR R (Fin N × Fin d) m →ₐ[R] JetR R' (Fin n × Fin d) m}
    (hΘ : IsMove a Θ) {X Y : Scheme.{0}} (q : X ⟶ Y)
    (r : ∀ m, Spec (CommRingCat.of (JetR R' (Fin n × Fin d) m)) ⟶ X)
    (p : ∀ m, Spec (CommRingCat.of (JetR R (Fin N × Fin d) m)) ⟶ Y)
    (h : ∀ m, r m ≫ q = (spMap (Θ m)).left ≫ p m) (U : Y.Opens) (f : Γ(Y, U)) (g : PS R N d)
    (hg : HasSer p U f g) :
    HasSer r (q ⁻¹ᵁ U) ((q.app U).hom f) (ev a (MvPowerSeries.map (algebraMap R R') g)) := by sorry
