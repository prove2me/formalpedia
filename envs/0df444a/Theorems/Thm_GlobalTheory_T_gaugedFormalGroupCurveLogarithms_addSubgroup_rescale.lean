-- Prove2me | Theorems.Thm_GlobalTheory_T_gaugedFormalGroupCurveLogarithms_addSubgroup_rescale
-- name    : GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-27T05:40:31.052621+00:00
-- url     : https://prove2.me/theorems/dc07cb96-458c-53e1-963d-70bf75311942
-- title:
--   T: gauged Formal Group Curve Logarithms add Subgroup rescale
-- statement:
--   The T construction uses the gauged Formal Group Curve Logarithms add Subgroup rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupResca
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
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

theorem GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, (0 ∈ Cv X V g) ∧ (∀ a ∈ Cv X V g, ∀ b ∈ Cv X V g, a + b ∈ Cv X V g) ∧ (∀ a ∈ Cv X V g, -a ∈ Cv X V g) ∧ (∀ s : C, V.Ge 0 s → ∀ a ∈ Cv X V g, ((fun i => PowerSeries.rescale s (a.1 i), fun q => PowerSeries.rescale s (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g) := by sorry
