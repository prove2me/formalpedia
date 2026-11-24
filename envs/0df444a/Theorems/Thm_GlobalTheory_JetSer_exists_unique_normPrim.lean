-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_exists_unique_normPrim
-- name    : GlobalTheory.JetSer.exists_unique_normPrim
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:41:48.750779+00:00
-- url     : https://prove2.me/theorems/3e357253-f9bb-492f-af77-da6994d93a1b
-- title:
--   Jet Ser: exists unique norm Prim
-- statement:
--   The Jet Ser construction uses the exists unique norm Prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsUniqueNormPrim.lean#L79-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsUniqueNormPrim.lean#L79-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.JetSer.exists_unique_normPrim : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (w : G ⟶ G) [IsMonHom w],
    LBIso Lr.L (cubeLB G ![𝟙 G, w] Lr.L) →
    (∃ ρ : LB.Gen (LB.LinComb Lr.L (primφ w) primε), ρ.IsGen ∧
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ (eSec G)) Lr.rig) ∧
    (Function.Surjective G.hom.appTop.hom → ∀ ρ ρ' : LB.Gen (LB.LinComb Lr.L (primφ w) primε), ρ.IsGen → ρ'.IsGen →
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ (eSec G)) Lr.rig →
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ' (eSec G)) Lr.rig → ρ.s = ρ'.s) := by sorry
