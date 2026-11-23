-- Prove2me | Theorems.Thm_GlobalTheory_fourier_inv_sixtythree
-- name    : GlobalTheory.fourier_inv_sixtythree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:53.321945+00:00
-- url     : https://prove2.me/theorems/b8b0a0d6-c19b-49e5-9db0-811e5dec79ce
-- title:
--   Global Theory: fourier inv sixtythree
-- statement:
--   The Global Theory construction uses the fourier inv sixtythree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/NoNormTwelveOrderSixtythree.lean#L22-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/NoNormTwelveOrderSixtythree.lean#L22-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormTwelveOrderSixtythree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory

theorem GlobalTheory.fourier_inv_sixtythree (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63) (m : ℕ)
    (hm : m < 63) :
    ∑ j ∈ Finset.range 63, (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * m))
      = 63 * (c m : ℂ) := by sorry
