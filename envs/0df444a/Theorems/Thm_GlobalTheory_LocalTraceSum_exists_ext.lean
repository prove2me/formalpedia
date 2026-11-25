-- Prove2me | Theorems.Thm_GlobalTheory_LocalTraceSum_exists_ext
-- name    : GlobalTheory.LocalTraceSum.exists_ext
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:27:11.187795+00:00
-- url     : https://prove2.me/theorems/f47d234e-0fc8-4d6e-be51-591ef531dc34
-- title:
--   Local Trace Sum: exists ext
-- statement:
--   The Local Trace Sum construction uses the exists ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L117-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L117-L183

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
variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[l] K] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

theorem GlobalTheory.LocalTraceSum.exists_ext (hc : Continuous (algebraMap ℚ_[l] K)) (ι : F →+* K) (hι : DenseRange ι)
    (σ : F →+* Ω) (h : ∀ a : F, valuation K (ι a) < 1 → ‖σ a‖ ≤ 1) :
    ∃ τ : K →ₐ[ℚ_[l]] Ω, ∀ a, τ (ι a) = σ a := by sorry
