-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_smul_mem_cyclotomicCompletion
-- name    : GroundTheory.PAdicHodge.smul_mem_cyclotomicCompletion
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:52.076322+00:00
-- url     : https://prove2.me/theorems/3124453b-7657-4844-bf51-2d9309bb0184
-- title:
--   PAdic Hodge: smul mem cyclotomic Completion
-- statement:
--   The PAdic Hodge construction uses the smul mem cyclotomic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateNormalizedTrace.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TateNormalizedTrace.lean#L146-L148

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
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
open IntermediateField Module Set
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]
variable {K}

theorem GroundTheory.PAdicHodge.smul_mem_cyclotomicCompletion (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : σ • x ∈ cyclotomicCompletion K := by sorry
