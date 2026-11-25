-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_exists_pow_le_span_sup_pow_succ
-- name    : GlobalTheory.JetSer.exists_pow_le_span_sup_pow_succ
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:12:58.481654+00:00
-- url     : https://prove2.me/theorems/668611a5-50a5-5456-8328-eae48ba5f60d
-- title:
--   Jet Ser: exists pow le span sup pow succ
-- statement:
--   The Jet Ser construction uses the exists pow le span sup pow succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/LocallyOfFiniteTypePullbackUnit.lean#L45-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/LocallyOfFiniteTypePullbackUnit.lean#L45-L135

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

theorem GlobalTheory.JetSer.exists_pow_le_span_sup_pow_succ : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] (f : G ⟶ G), η[G] ≫ f = η[G] → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)), Finite {x : Over.mk t ⟶ G // x ≫ f = 1}) → ∀ (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ φ : Pt k 1 d, GlobalTheory.JetSer.IsMapOf x x f φ → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ^ M ≤ Ideal.span (Set.range φ) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ^ (M + 1) := by sorry
