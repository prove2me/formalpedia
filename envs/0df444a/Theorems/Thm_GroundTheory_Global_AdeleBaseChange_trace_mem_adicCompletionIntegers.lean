-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_trace_mem_adicCompletionIntegers
-- name    : GroundTheory.Global.AdeleBaseChange.trace_mem_adicCompletionIntegers
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:14:47.554858+00:00
-- url     : https://prove2.me/theorems/c697a318-e1f7-4fd1-90ea-bfdc6cb1cb28
-- title:
--   Adele Base Change: trace mem adic Completion Integers
-- statement:
--   The Adele Base Change construction uses the trace mem adic Completion Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteCoord.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteCoord.lean#L17-L28

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.AdeleBaseChange.trace_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] {y : w.adicCompletion L}
    (hy : y ∈ w.adicCompletionIntegers L) :
    Algebra.trace (v.adicCompletion K) (w.adicCompletion L) y ∈ v.adicCompletionIntegers K := by sorry
