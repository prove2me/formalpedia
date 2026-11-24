-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_coe_restrictAut
-- name    : GroundTheory.PAdicHodge.coe_restrictAut
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:42.730975+00:00
-- url     : https://prove2.me/theorems/88acadc8-8cf2-4a84-9ec9-c66e19d806a8
-- title:
--   PAdic Hodge: coe restrict Aut
-- statement:
--   The PAdic Hodge construction uses the coe restrict Aut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWGlue.lean#L20-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWGlue.lean#L20-L36

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FWGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem GroundTheory.PAdicHodge.coe_restrictAut (Ω : IntermediateField F E) (τ : Ω ≃ₐ[F] Ω) (N : IntermediateField F E)
    (hN : N ≤ Ω) [Normal F N] (y : N) :
    ((restrictAut Ω τ N hN y : N) : E) = ((τ ⟨y, hN y.2⟩ : Ω) : E) := by sorry
