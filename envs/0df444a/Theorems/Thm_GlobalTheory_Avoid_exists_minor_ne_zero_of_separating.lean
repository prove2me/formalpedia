-- Prove2me | Theorems.Thm_GlobalTheory_Avoid_exists_minor_ne_zero_of_separating
-- name    : GlobalTheory.Avoid.exists_minor_ne_zero_of_separating
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:58:06.168671+00:00
-- url     : https://prove2.me/theorems/ecdae4e6-d256-4900-a858-02e905ee445c
-- title:
--   Avoid: exists minor ne zero of separating
-- statement:
--   The Avoid construction uses the exists minor ne zero of separating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisMapOfLiftBaseChangeSurjective.lean#L74-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisMapOfLiftBaseChangeSurjective.lean#L74-L92

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

theorem GlobalTheory.Avoid.exists_minor_ne_zero_of_separating {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [LinearOrder ι] (c : ι → Dual K V)
    (hc : ∀ v : V, (∀ j, c j v = 0) → v = 0) {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Set.powersetCard ι r, pairingDual K V r (ιMulti_family K r c J) x ≠ 0 := by sorry
