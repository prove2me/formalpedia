-- Prove2me | Theorems.Thm_GlobalTheory_intSymm_posSemidef_real
-- name    : GlobalTheory.intSymm_posSemidef_real
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:56:26.423497+00:00
-- url     : https://prove2.me/theorems/b2acb85b-cf50-4b03-9df7-99ed402e6d58
-- title:
--   Global Theory: int Symm pos Semidef real
-- statement:
--   The Global Theory construction uses the int Symm pos Semidef real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PosSemidefRealOfIntQuadFormNonneg.lean#L7-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PosSemidefRealOfIntQuadFormNonneg.lean#L7-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PosSemidefRealOfIntQuadFormNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.intSymm_posSemidef_real :
    ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm →
      (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) →
      (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by sorry
