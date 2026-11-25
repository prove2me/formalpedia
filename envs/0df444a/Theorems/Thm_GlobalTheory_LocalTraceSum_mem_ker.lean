-- Prove2me | Theorems.Thm_GlobalTheory_LocalTraceSum_mem_ker
-- name    : GlobalTheory.LocalTraceSum.mem_ker
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:57.147819+00:00
-- url     : https://prove2.me/theorems/3bb9e2d5-02d1-5b26-b310-5f3b063b56a8
-- title:
--   Local Trace Sum: mem ker
-- statement:
--   The Local Trace Sum construction uses the mem ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L82-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L82-L82

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
variable {F : Type} [Field F] [NumberField F] {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω]

theorem GlobalTheory.LocalTraceSum.mem_ker (σ : F →+* Ω) (a : 𝓞 F) : a ∈ ker σ ↔ ‖σ a‖ < 1 := by sorry
