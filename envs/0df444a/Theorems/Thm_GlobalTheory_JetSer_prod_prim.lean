-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_prod_prim
-- name    : GlobalTheory.JetSer.prod_prim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:54.458617+00:00
-- url     : https://prove2.me/theorems/f0ffe8fc-2fbc-4836-a4b0-4b87b48644ca
-- title:
--   Jet Ser: prod prim
-- statement:
--   The Jet Ser construction uses the prod prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsUniqueNormPrim.lean#L67-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsUniqueNormPrim.lean#L67-L77

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

theorem GlobalTheory.JetSer.prod_prim {S : Scheme.{0}} {G T : Over S} [GrpObj G] (w : G ⟶ G) (x : T ⟶ G) {U : Type} [CommGroup U]
    (h : (T.left ⟶ G.left) → U) :
    ∏ i, h (x.left ≫ primφ w i) ^ primε i =
      h x.left * (h (x * (x ≫ w)).left)⁻¹ * h x.left * h (x ≫ w).left * (h (1 : T ⟶ G).left)⁻¹ := by sorry
