-- Prove2me | Theorems.Thm_GlobalTheory_LocalTraceSum_norm_lt_one
-- name    : GlobalTheory.LocalTraceSum.norm_lt_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:30:00.472267+00:00
-- url     : https://prove2.me/theorems/f552905b-82e5-50ba-8706-26fee76e2d51
-- title:
--   Local Trace Sum: norm lt one
-- statement:
--   The Local Trace Sum construction uses the norm lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L52-L56

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocalTraceSum
open Filter Topology TensorProduct
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {l : ℕ} [Fact l.Prime] [Algebra ℚ_[l] K]
variable {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

theorem GlobalTheory.LocalTraceSum.norm_lt_one [FiniteDimensional ℚ_[l] K] (hc : Continuous (algebraMap ℚ_[l] K))
    (τ : K →ₐ[ℚ_[l]] Ω) {x : K} (h : valuation K x < 1) : ‖τ x‖ < 1 := by sorry
