-- Prove2me | Theorems.Thm_GlobalTheory_AdicQuot_ker_psi
-- name    : GlobalTheory.AdicQuot.ker_psi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:54:41.256452+00:00
-- url     : https://prove2.me/theorems/a5f4202a-f642-48a5-93b7-d93aca6b76fe
-- title:
--   Adic Quot: ker psi
-- statement:
--   The Adic Quot construction uses the ker psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionQuotientRingEquiv.lean#L53-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionQuotientRingEquiv.lean#L53-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.AdicQuot
open AdicCompletion
variable {A : Type} [CommRing A] (J q : Ideal A)

theorem GlobalTheory.AdicQuot.ker_psi [IsNoetherianRing A] :
    RingHom.ker (psi J q) = q.map (algebraMap A (AdicCompletion J A)) := by sorry
