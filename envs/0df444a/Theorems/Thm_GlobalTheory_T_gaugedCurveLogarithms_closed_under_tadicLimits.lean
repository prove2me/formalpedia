-- Prove2me | Theorems.Thm_GlobalTheory_T_gaugedCurveLogarithms_closed_under_tadicLimits
-- name    : GlobalTheory.T.gaugedCurveLogarithms_closed_under_tadicLimits
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:46:40.44009+00:00
-- url     : https://prove2.me/theorems/b0505bfd-c21b-4560-9a16-77c55214b6da
-- title:
--   T: gauged Curve Logarithms closed under tadic Limits
-- statement:
--   The T construction uses the gauged Curve Logarithms closed under tadic Limits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugedCurveLogarithmsClosedUnderTadicLimitsStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugedCurveLogarithmsClosedUnderTadicLimitsStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimits
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimitsStatement
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.gaugedCurveLogarithms_closed_under_tadicLimits : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (a : ℕ → ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) (b : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))), (∀ n, a n ∈ Cv X V g) → (∀ m, ∃ n0, ∀ n ≥ n0, (∀ i, PowerSeries.coeff m ((a n).1 i) = PowerSeries.coeff m (b.1 i)) ∧ ∀ q, PowerSeries.coeff m ((a n).2 q) = PowerSeries.coeff m (b.2 q)) → b ∈ Cv X V g := by sorry
