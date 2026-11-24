-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_mem_sup_pow_of_toJet_mem_map
-- name    : GlobalTheory.JetSer.mem_sup_pow_of_toJet_mem_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:44:25.03008+00:00
-- url     : https://prove2.me/theorems/659db3a3-6a16-45b9-a195-e281fbf3c742
-- title:
--   Jet Ser: mem sup pow of to Jet mem map
-- statement:
--   The Jet Ser construction uses the mem sup pow of to Jet mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/LocallyOfFiniteTypePullbackUnit.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/LocallyOfFiniteTypePullbackUnit.lean#L17-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RepJetAugCompTrunc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniversalThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_LocallyOfFiniteTypePullbackUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer

theorem GlobalTheory.JetSer.mem_sup_pow_of_toJet_mem_map {R : Type} [CommRing R] {κ : Type} [Finite κ] (m : ℕ)
    (I : Ideal (MvPowerSeries κ R)) (g : MvPowerSeries κ R) (hg : toJet m g ∈ I.map (toJetHom R κ m)) :
    g ∈ I ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R)) ^ (m + 1) := by sorry
