-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_restrictAut_mul
-- name    : GroundTheory.PAdicHodge.restrictAut_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:22.336855+00:00
-- url     : https://prove2.me/theorems/c065abce-94f1-40b5-a8c6-b5fe5aa9e056
-- title:
--   PAdic Hodge: restrict Aut mul
-- statement:
--   The PAdic Hodge construction uses the restrict Aut mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWGlue.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWGlue.lean#L38-L46

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

theorem GroundTheory.PAdicHodge.restrictAut_mul (Ω : IntermediateField F E) (τ₁ τ₂ : Ω ≃ₐ[F] Ω) (N : IntermediateField F E)
    (hN : N ≤ Ω) [Normal F N] :
    restrictAut Ω (τ₁ * τ₂) N hN = restrictAut Ω τ₁ N hN * restrictAut Ω τ₂ N hN := by sorry
