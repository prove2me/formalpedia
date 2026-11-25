-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_mem_cyclotomicCompletion_of_forall_smul_eq
-- name    : GroundTheory.PAdicHodge.mem_cyclotomicCompletion_of_forall_smul_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:11:23.844026+00:00
-- url     : https://prove2.me/theorems/02f40691-640f-43cd-9a4a-233f66f847f6
-- title:
--   PAdic Hodge: mem cyclotomic Completion of forall smul eq
-- statement:
--   The PAdic Hodge construction uses the mem cyclotomic Completion of forall smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean#L210-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean#L210-L216

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField UniformSpace
variable {p : ℕ} [hp : Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem GroundTheory.PAdicHodge.mem_cyclotomicCompletion_of_forall_smul_eq {x : ℂ_[p]}
    (hx : ∀ σ ∈ cyclotomicLimitGal K, σ • x = x) : x ∈ cyclotomicCompletion K := by sorry
