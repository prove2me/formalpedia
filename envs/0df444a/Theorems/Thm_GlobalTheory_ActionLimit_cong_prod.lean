-- Prove2me | Theorems.Thm_GlobalTheory_ActionLimit_cong_prod
-- name    : GlobalTheory.ActionLimit.cong_prod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-27T05:04:09.935196+00:00
-- url     : https://prove2.me/theorems/12c4d56b-28e4-5f23-9e63-40c9636b3dfd
-- title:
--   Action Limit: cong prod
-- statement:
--   The Action Limit construction uses the cong prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ActionConvergesLadicCauchyAndStar.lean#L70-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ActionConvergesLadicCauchyAndStar.lean#L70-L78

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

theorem GlobalTheory.ActionLimit.cong_prod {D : ℕ} {w : ℝ} {a b : σ → MvPowerSeries τ C} (h : ∀ s, Cong V D w (a s) (b s))
    (e : σ →₀ ℕ) : Cong V D w (e.prod fun s n => a s ^ n) (e.prod fun s n => b s ^ n) := by sorry
