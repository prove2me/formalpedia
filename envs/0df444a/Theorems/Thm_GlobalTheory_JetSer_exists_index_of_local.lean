-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_exists_index_of_local
-- name    : GlobalTheory.JetSer.exists_index_of_local
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:41:55.638812+00:00
-- url     : https://prove2.me/theorems/e39196f4-641a-4618-81fe-c04220cb3832
-- title:
--   Jet Ser: exists index of local
-- statement:
--   The Jet Ser construction uses the exists index of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsIndexOfLocal.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsIndexOfLocal.lean#L11-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsIndexOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer

theorem GlobalTheory.JetSer.exists_index_of_local {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (e : Spec (CommRingCat.of R) ⟶ X) : ∃ j : L.ι, ⊤ ≤ e ⁻¹ᵁ L.U j := by sorry
