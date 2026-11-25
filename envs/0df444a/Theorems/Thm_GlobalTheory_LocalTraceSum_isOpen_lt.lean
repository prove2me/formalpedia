-- Prove2me | Theorems.Thm_GlobalTheory_LocalTraceSum_isOpen_lt
-- name    : GlobalTheory.LocalTraceSum.isOpen_lt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:30:10.324403+00:00
-- url     : https://prove2.me/theorems/8ddcd37d-a96d-5008-a8cc-b9a49c1f96d5
-- title:
--   Local Trace Sum: is Open lt
-- statement:
--   The Local Trace Sum construction uses the is Open lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L20-L26

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

theorem GlobalTheory.LocalTraceSum.isOpen_lt (γ : ValueGroupWithZero K) : IsOpen {x : K | valuation K x < γ} := by sorry
