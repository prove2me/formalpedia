-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_finsum_rootsOfUnity_pow_mul_star
-- name    : GlobalTheory.CuspGL.finsum_rootsOfUnity_pow_mul_star
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:28.602406+00:00
-- url     : https://prove2.me/theorems/fc29fc3a-ac9e-4d2f-b805-882492ab53cc
-- title:
--   Cusp GL: finsum roots Of Unity pow mul star
-- statement:
--   The Cusp GL construction uses the finsum roots Of Unity pow mul star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FrobeniusTorusCharacterOrthogonality.lean#L9-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FrobeniusTorusCharacterOrthogonality.lean#L9-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusCharacterOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.finsum_rootsOfUnity_pow_mul_star {K : Type} [Field K] (θ : K →* ℂ) {N : ℕ} (hN : 0 < N)
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) (hω : IsPrimitiveRoot (θ ζ) N) (k l : ℕ) :
    ∑ᶠ α ∈ {α : K | α ^ N = 1}, θ α ^ k * star (θ α ^ l) =
      if k ≡ l [MOD N] then ((N : ℕ) : ℂ) else 0 := by sorry
