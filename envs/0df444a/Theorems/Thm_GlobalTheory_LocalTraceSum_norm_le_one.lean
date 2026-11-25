-- Prove2me | Theorems.Thm_GlobalTheory_LocalTraceSum_norm_le_one
-- name    : GlobalTheory.LocalTraceSum.norm_le_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:30:22.704931+00:00
-- url     : https://prove2.me/theorems/d7077288-4a5e-54c7-a504-aa31927a1d14
-- title:
--   Local Trace Sum: norm le one
-- statement:
--   The Local Trace Sum construction uses the norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L94-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L94-L102

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

theorem GlobalTheory.LocalTraceSum.norm_le_one (σ : F →+* Ω) (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal = ker σ)
    {a : F} (ha : p.valuation F a ≤ 1) : ‖σ a‖ ≤ 1 := by sorry
