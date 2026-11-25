-- Prove2me | Theorems.Thm_GlobalTheory_adicCompletion_injective_ringHom_of_finite
-- name    : GlobalTheory.adicCompletion_injective_ringHom_of_finite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:07.477458+00:00
-- url     : https://prove2.me/theorems/8086ab37-e338-42b5-9d0e-cb2cf321aa23
-- title:
--   Global Theory: adic Completion injective ring Hom of finite
-- statement:
--   The Global Theory construction uses the adic Completion injective ring Hom of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsInjectiveAdicCompletionMapOfFinite.lean#L19-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsInjectiveAdicCompletionMapOfFinite.lean#L19-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsInjectiveAdicCompletionMapOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.adicCompletion_injective_ringHom_of_finite
    (D N : Type) [CommRing D] [CommRing N] [IsNoetherianRing D] [Algebra D N]
    [Module.Finite D N] (hinj : Function.Injective (algebraMap D N)) (J : Ideal D) :
    ∃ f : AdicCompletion J D →+* AdicCompletion (J.map (algebraMap D N)) N,
      Function.Injective f := by sorry
