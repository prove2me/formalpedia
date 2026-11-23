-- Prove2me | Theorems.Thm_GlobalTheory_T_monicFactorizationConvolution_finite_comm_assoc_add
-- name    : GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:58.855533+00:00
-- url     : https://prove2.me/theorems/63d792d0-740c-425d-9521-2647c8e46f9a
-- title:
--   T: monic Factorization Convolution finite comm assoc add
-- statement:
--   The T construction uses the monic Factorization Convolution finite comm assoc add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MonicFactorizationConvolutionFiniteCommAssocAddStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MonicFactorizationConvolutionFiniteCommAssocAddStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAdd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAddStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add : ∀ (F : Type) [Field F] (P : F[X]), P.Monic → {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite ∧ ∀ a b c : F[X] → ℂ, conv a b P = conv b a P ∧ conv (conv a b) c P = conv a (conv b c) P ∧ conv (a + b) c P = conv a c P + conv b c P ∧ conv (a - b) c P = conv a c P - conv b c P := by sorry
