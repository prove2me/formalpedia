-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_IsPurePair_of_equiv
-- name    : GlobalTheory.WeilDeligne.IsPurePair.of_equiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:54:59.940801+00:00
-- url     : https://prove2.me/theorems/bf245b79-35d1-5d98-8f68-f4b70e761a8d
-- title:
--   Is Pure Pair: of equiv
-- statement:
--   The Is Pure Pair construction uses the of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L127-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L127-L150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem GlobalTheory.WeilDeligne.IsPurePair.of_equiv {q : ℝ} {f N : End ℂ V} {g M : End ℂ V'} (e : V ≃ₗ[ℂ] V')
    (he : ∀ v, e (f v) = g (e v)) (hN : ∀ v, e (N v) = M (e v)) (hp : IsPurePair q f N) :
    IsPurePair q g M := by sorry
