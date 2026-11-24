-- Prove2me | Theorems.Thm_GlobalTheory_multilinear_mem_span_of_mem_span
-- name    : GlobalTheory.multilinear_mem_span_of_mem_span
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:39.083504+00:00
-- url     : https://prove2.me/theorems/6ef85b2b-9119-43ca-8e3b-4faac3544dd9
-- title:
--   Global Theory: multilinear mem span of mem span
-- statement:
--   The Global Theory construction uses the multilinear mem span of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeylTensorCoefSpaceLeSpanPureTensors.lean#L12-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeylTensorCoefSpaceLeSpanPureTensors.lean#L12-L52

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceLeSpanPureTensors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
open GlobalTheory

theorem GlobalTheory.multilinear_mem_span_of_mem_span {K ι M N : Type} [Field K] [Fintype ι]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (m : MultilinearMap K (fun _ : ι => M) N) (S : ι → Set M) (f : ι → M)
    (hf : ∀ τ, f τ ∈ Submodule.span K (S τ)) :
    m f ∈ Submodule.span K {P | ∃ g : ι → M, (∀ τ, g τ ∈ S τ) ∧ P = m g} := by sorry
