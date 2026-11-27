-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_CvDiv_step
-- name    : GlobalTheory.RowLaw.CvDiv.step
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:53:19.141828+00:00
-- url     : https://prove2.me/theorems/8672a5ab-141f-5cf3-ab84-92890fc01e9f
-- title:
--   Cv Div: step
-- statement:
--   The Cv Div construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CurveLogarithmsInvNatCastSmulMem.lean#L48-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CurveLogarithmsInvNatCastSmulMem.lean#L48-L82

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CurveLogarithmsInvNatCastSmulMem
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
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvDiv
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem GlobalTheory.RowLaw.CvDiv.step {X : RawChart C d I κ} {V : VF C} (hX : RLaw X V) (g : Fin 2) {c : C} (hc : V.Ge 0 c)
    (m : ℕ) {a : (κ → PowerSeries C) × (JJ I g → PowerSeries C)} (ha : a ∈ Cv X V g)
    (hv : ∀ i, ∀ k < m, PowerSeries.coeff k (a.1 i) = 0) :
    ∃ b ∈ Cv X V g, ∀ k ≤ m, (∀ i, PowerSeries.coeff k (b.1 i) = c * PowerSeries.coeff k (a.1 i)) ∧
      ∀ q, PowerSeries.coeff k (b.2 q) = c * PowerSeries.coeff k (a.2 q) := by sorry
