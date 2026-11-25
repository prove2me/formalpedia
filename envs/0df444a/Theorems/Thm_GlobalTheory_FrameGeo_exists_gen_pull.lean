-- Prove2me | Theorems.Thm_GlobalTheory_FrameGeo_exists_gen_pull
-- name    : GlobalTheory.FrameGeo.exists_gen_pull
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:37:56.259016+00:00
-- url     : https://prove2.me/theorems/9828cee9-578e-45d5-955c-730e0538a44c
-- title:
--   Frame Geo: exists gen pull
-- statement:
--   The Frame Geo construction uses the exists gen pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ThreePointSeriesExponentialOfDefect.lean#L75-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ThreePointSeriesExponentialOfDefect.lean#L75-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FrameGeo
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem GlobalTheory.FrameGeo.exists_gen_pull (Lr : RigLB G) (c : CubicalStr G Lr) {O : Type} [CommRing O] [StarRing O]
    (act : Geo.Tor.OAct O G) (a w0 : O) (N : ℕ) (hN : a * star a = (N : O))
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)) (hu : u.IsGen)
    (ρ : LB.Gen (LB.LinComb Lr.L (primφ (act.act w0)) primε)) (hρ : ρ.IsGen) :
    ∃ mu : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![𝟙 G.left, (act.act a).left] ![(N : ℤ), -1]), mu.IsGen ∧
      ∀ (T : Over S) (y : T ⟶ G) (z : T.left) (J), Good Lr.L z J →
        val mu y.left z J * val ρ (y ≫ act.act a).left z J *
          ∏ i ∈ Finset.range N, cubV c z J y (y ≫ act.act ((i : O) * w0)) (y ≫ act.act w0) =
        (val₂ u z J y (y ≫ act.act (w0 * a)))⁻¹ * val ρ y.left z J ^ N := by sorry
