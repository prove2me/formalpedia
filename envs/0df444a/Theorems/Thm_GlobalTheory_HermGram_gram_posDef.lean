-- Prove2me | Theorems.Thm_GlobalTheory_HermGram_gram_posDef
-- name    : GlobalTheory.HermGram.gram_posDef
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:19:27.948552+00:00
-- url     : https://prove2.me/theorems/dc81956b-1253-4694-a82b-3eff7c5c07ab
-- title:
--   Herm Gram: gram pos Def
-- statement:
--   The Herm Gram construction uses the gram pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosDefRealGramPairHermitianForms.lean#L31-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosDefRealGramPairHermitianForms.lean#L31-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefRealGramPairHermitianForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.HermGram

theorem GlobalTheory.HermGram.gram_posDef {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) :
    (Matrix.of fun k l => (e k ⬝ᵥ H.mulVec (star (e l))).re).PosDef := by sorry
