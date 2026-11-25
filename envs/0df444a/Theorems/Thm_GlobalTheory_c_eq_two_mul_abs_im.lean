-- Prove2me | Theorems.Thm_GlobalTheory_c_eq_two_mul_abs_im
-- name    : GlobalTheory.c_eq_two_mul_abs_im
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:12:10.141544+00:00
-- url     : https://prove2.me/theorems/cd03a240-6669-4cd3-98a6-73ae6dfa26e4
-- title:
--   Global Theory: c eq two mul abs im
-- statement:
--   The Global Theory construction uses the c eq two mul abs im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/SumCMulImHermCEqSignMulTrace.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/SumCMulImHermCEqSignMulTrace.lean#L31-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_SumCMulImHermCEqSignMulTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open NumberField

theorem GlobalTheory.c_eq_two_mul_abs_im {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r : ℕ}
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : X.Ψ) : X.c τ = 2 * |(τ.1 X.ξ0).im| := by sorry
