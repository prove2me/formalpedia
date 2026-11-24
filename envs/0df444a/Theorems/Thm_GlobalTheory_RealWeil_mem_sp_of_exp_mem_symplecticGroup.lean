-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_mem_sp_of_exp_mem_symplecticGroup
-- name    : GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:16:05.441805+00:00
-- url     : https://prove2.me/theorems/9cda65f7-ccca-443b-95c7-ec6d5e89add2
-- title:
--   Real Weil: mem sp of exp mem symplectic Group
-- statement:
--   The Real Weil construction uses the mem sp of exp mem symplectic Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro.lean#L6-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro.lean#L6-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.RealWeil

theorem GlobalTheory.RealWeil.mem_sp_of_exp_mem_symplecticGroup (l : Type) [Fintype l] [DecidableEq l]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) :
    X ∈ LieAlgebra.Symplectic.sp l ℝ := by sorry
