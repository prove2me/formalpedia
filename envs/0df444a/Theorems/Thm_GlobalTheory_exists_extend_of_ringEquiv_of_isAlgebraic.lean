-- Prove2me | Theorems.Thm_GlobalTheory_exists_extend_of_ringEquiv_of_isAlgebraic
-- name    : GlobalTheory.exists_extend_of_ringEquiv_of_isAlgebraic
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:30.479922+00:00
-- url     : https://prove2.me/theorems/7df023a0-ecfe-4973-a0ed-33fa4d0c9777
-- title:
--   Global Theory: exists extend of ring Equiv of is Algebraic
-- statement:
--   The Global Theory construction uses the exists extend of ring Equiv of is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteNormalAdjoinAlgebraic.lean#L5-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteNormalAdjoinAlgebraic.lean#L5-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteNormalAdjoinAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_extend_of_ringEquiv_of_isAlgebraic {K L M F : Type} [Field K] [Field L] [Field M] [Field F]
    [IsAlgClosed F] [Algebra L M] [Algebra.IsAlgebraic L M] (φ : K ≃+* L) (g : K →+* F) :
    ∃ g' : M →+* F, g'.comp ((algebraMap L M).comp φ.toRingHom) = g := by sorry
