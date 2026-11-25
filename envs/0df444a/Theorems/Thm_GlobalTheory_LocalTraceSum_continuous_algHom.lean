-- Prove2me | Theorems.Thm_GlobalTheory_LocalTraceSum_continuous_algHom
-- name    : GlobalTheory.LocalTraceSum.continuous_algHom
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:45.265062+00:00
-- url     : https://prove2.me/theorems/d413d310-97e0-4cee-8d99-aa1c10951148
-- title:
--   Local Trace Sum: continuous alg Hom
-- statement:
--   The Local Trace Sum construction uses the continuous alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L46-L50

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

theorem GlobalTheory.LocalTraceSum.continuous_algHom [FiniteDimensional ℚ_[l] K] (hc : Continuous (algebraMap ℚ_[l] K))
    (τ : K →ₐ[ℚ_[l]] Ω) : Continuous τ := by sorry
