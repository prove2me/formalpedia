-- Prove2me | Theorems.Thm_GlobalTheory_ChartBaseChange_exists_move
-- name    : GlobalTheory.ChartBaseChange.exists_move
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:12.571869+00:00
-- url     : https://prove2.me/theorems/b1e180d1-83b6-4a43-b3dc-d9cc9759e40e
-- title:
--   Chart Base Change: exists move
-- statement:
--   The Chart Base Change construction uses the exists move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L359-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L359-L370

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
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)

theorem GlobalTheory.ChartBaseChange.exists_move (hJ : JetAlgSt) {x : Fam G (Fin d)} {x' : Fam G' (Fin d)}
    (hx' : ∀ m, push hπ (x' m) = spMap (jetCoeff R R' (Fin d) m) ≫ x m)
    (a : Fin N → Pt R' n d) (y : Fin N → Fam G' (Fin n × Fin d)) (hy : ∀ i, Rep x' (a i) (y i)) :
    ∃ (Θ : ∀ m, JetR R (Fin N × Fin d) m →ₐ[R] JetR R' (Fin n × Fin d) m) (t : Fin N → Fam G (Fin N × Fin d)),
      IsMove a Θ ∧ (∀ i, Rep x (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R d i) (t i)) ∧
      ∀ i m, push hπ (y i m) = spMap (Θ m) ≫ t i m := by sorry
