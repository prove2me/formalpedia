-- Prove2me | Theorems.Thm_GlobalTheory_Avoid_exists_orderEmbedding_minor_ne_zero
-- name    : GlobalTheory.Avoid.exists_orderEmbedding_minor_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:49.640527+00:00
-- url     : https://prove2.me/theorems/1df10146-10d2-4e6e-bb22-a941633ec6d4
-- title:
--   Avoid: exists order Embedding minor ne zero
-- statement:
--   The Avoid construction uses the exists order Embedding minor ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisMapOfLiftBaseChangeSurjective.lean#L116-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisMapOfLiftBaseChangeSurjective.lean#L116-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisMapOfLiftBaseChangeSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open scoped TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.Avoid
open exteriorPower
open Module Function
open scoped TensorProduct Pointwise
open exteriorPower

theorem GlobalTheory.Avoid.exists_orderEmbedding_minor_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [LinearOrder ι] (c : ι → Dual K V)
    (hc : Submodule.span K (Set.range c) = ⊤) {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Fin r ↪o ι, pairingDual K V r (ιMulti K r fun k => c (J k)) x ≠ 0 := by sorry
