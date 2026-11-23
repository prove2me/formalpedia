-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_prod_lam
-- name    : GlobalTheory.JetSer.prod_lam
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:46.321338+00:00
-- url     : https://prove2.me/theorems/42d2b439-7b78-4090-a72b-11d153ffaf3b
-- title:
--   Jet Ser: prod lam
-- statement:
--   The Jet Ser construction uses the prod lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsUniqueNormPrim.lean#L46-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsUniqueNormPrim.lean#L46-L65

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

theorem GlobalTheory.JetSer.prod_lam {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] (x y : T ⟶ G) {U : Type} [CommGroup U]
    (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum G ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by sorry
