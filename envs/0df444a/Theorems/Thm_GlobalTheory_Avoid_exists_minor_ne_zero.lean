-- Prove2me | Theorems.Thm_GlobalTheory_Avoid_exists_minor_ne_zero
-- name    : GlobalTheory.Avoid.exists_minor_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:27.716043+00:00
-- url     : https://prove2.me/theorems/8b05f0e3-cee8-506b-8ba9-be2f077c2b66
-- title:
--   Avoid: exists minor ne zero
-- statement:
--   The Avoid construction uses the exists minor ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisMapOfLiftBaseChangeSurjective.lean#L106-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisMapOfLiftBaseChangeSurjective.lean#L106-L110

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

theorem GlobalTheory.Avoid.exists_minor_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [LinearOrder ι] (c : Basis ι K (Dual K V))
    {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Set.powersetCard ι r, pairingDual K V r (ιMulti_family K r c J) x ≠ 0 := by sorry
