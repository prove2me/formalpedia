-- Prove2me | Theorems.Thm_GlobalTheory_ActionLimit_coeff_prod_high
-- name    : GlobalTheory.ActionLimit.coeff_prod_high
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:09:44.208725+00:00
-- url     : https://prove2.me/theorems/2c53ff36-37b1-422d-987e-8d2895432a32
-- title:
--   Action Limit: coeff prod high
-- statement:
--   The Action Limit construction uses the coeff prod high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ActionConvergesLadicCauchyAndStar.lean#L80-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ActionConvergesLadicCauchyAndStar.lean#L80-L93

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ActionConvergesLadicCauchyAndStar
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_prod

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
open GlobalTheory GlobalTheory.ActionLimit
open MvPowerSeries GlobalTheory.GaugeAdjoint
variable {C : Type} [Field C] {V : VF C} {σ τ : Type}

theorem GlobalTheory.ActionLimit.coeff_prod_high {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (e : σ →₀ ℕ) (μ : τ →₀ ℕ) (h : μ.degree < e.degree) :
    coeff μ (e.prod fun s n => a s ^ n) = 0 := by sorry
