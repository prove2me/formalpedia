-- Prove2me | Theorems.Thm_GlobalTheory_NormRos_exists_gen_of_lbIso
-- name    : GlobalTheory.NormRos.exists_gen_of_lbIso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:35.677894+00:00
-- url     : https://prove2.me/theorems/434683ca-88f8-4160-8915-8eb7748bba20
-- title:
--   Norm Ros: exists gen of lb Iso
-- statement:
--   The Norm Ros construction uses the exists gen of lb Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsGenRosati.lean#L15-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsGenRosati.lean#L15-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
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
open GlobalTheory GlobalTheory.NormRos
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.NormRos.exists_gen_of_lbIso {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k))), t.IsGen := by sorry
