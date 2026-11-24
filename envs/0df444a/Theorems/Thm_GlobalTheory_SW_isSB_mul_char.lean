-- Prove2me | Theorems.Thm_GlobalTheory_SW_isSB_mul_char
-- name    : GlobalTheory.SW.isSB_mul_char
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:40.221819+00:00
-- url     : https://prove2.me/theorems/01feaf78-a3b4-4bad-8a1f-90ec27170f9f
-- title:
--   SW: is SB mul char
-- statement:
--   The SW construction uses the is SB mul char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeisenbergOperatorRationalPointLaws.lean#L26-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeisenbergOperatorRationalPointLaws.lean#L26-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeisenbergOperatorRationalPointLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.isSB_mul_char {κ ι : Type} [Fintype κ] [Fintype ι] (a b : Matrix κ ι ℚ)
    (ψ : Matrix κ ι ℚ → ℂ) (h : IsSB ψ) :
    IsSB (fun x : Matrix κ ι ℚ => ψ x *
      cexp (Real.pi * I * ((∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) : ℂ))) := by sorry
