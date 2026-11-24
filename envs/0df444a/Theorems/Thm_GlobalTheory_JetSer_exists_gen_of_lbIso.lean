-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_exists_gen_of_lbIso
-- name    : GlobalTheory.JetSer.exists_gen_of_lbIso
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:16.694794+00:00
-- url     : https://prove2.me/theorems/9633b1ed-5c1f-493d-8c12-4f4632e85beb
-- title:
--   Jet Ser: exists gen of lb Iso
-- statement:
--   The Jet Ser construction uses the exists gen of lb Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsUniqueNormPrim.lean#L16-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsUniqueNormPrim.lean#L16-L37

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

theorem GlobalTheory.JetSer.exists_gen_of_lbIso {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (X ⟶ X)) (ε : K → ℤ)
    (H : LBIso L (LB.LinComb L φ ε)) :
    ∃ t : LB.Gen (LB.LinComb L (K := K ⊕ PUnit) (Sum.elim φ (fun _ => 𝟙 X)) (Sum.elim ε (fun _ => -1))), t.IsGen := by sorry
