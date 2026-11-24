-- Prove2me | Theorems.Thm_GlobalTheory_finrank_eq_mul_of_basis_tensor_self
-- name    : GlobalTheory.finrank_eq_mul_of_basis_tensor_self
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:47:29.714647+00:00
-- url     : https://prove2.me/theorems/9fd06957-a80b-435e-aaea-ea5187a5ac89
-- title:
--   Global Theory: finrank eq mul of basis tensor self
-- statement:
--   The Global Theory construction uses the finrank eq mul of basis tensor self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpanEqTopOfFinrankFibreEq.lean#L132-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpanEqTopOfFinrankFibreEq.lean#L132-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory
open TensorProduct Module

theorem GlobalTheory.finrank_eq_mul_of_basis_tensor_self (k B A : Type) [Field k] [CommRing B] [CommRing A]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Module.Finite k A] (r : ℕ)
    (hinj : Function.Injective (algebraMap B A))
    (hb : Nonempty (Module.Basis (Fin r) A (TensorProduct B A A))) :
    Module.finrank k A = r * Module.finrank k B := by sorry
