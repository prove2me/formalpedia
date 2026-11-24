-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_finrank_ker_lsmul_pow_quotient
-- name    : GlobalTheory.CuspGL.finrank_ker_lsmul_pow_quotient
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:32:43.031953+00:00
-- url     : https://prove2.me/theorems/e04d7138-a11f-4180-9d51-be70c51b230b
-- title:
--   Cusp GL: finrank ker lsmul pow quotient
-- statement:
--   The Cusp GL construction uses the finrank ker lsmul pow quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimaryEndomorphismCyclicDecompositionFinrankKer.lean#L10-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimaryEndomorphismCyclicDecompositionFinrankKer.lean#L10-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimaryEndomorphismCyclicDecompositionFinrankKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.finrank_ker_lsmul_pow_quotient {F : Type} [Field F] (f : F[X]) (hf : f ≠ 0) (e j : ℕ) :
    Module.finrank F (LinearMap.ker
      ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F)) =
      f.natDegree * min j e := by sorry
