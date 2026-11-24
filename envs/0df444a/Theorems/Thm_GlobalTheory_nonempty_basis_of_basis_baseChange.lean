-- Prove2me | Theorems.Thm_GlobalTheory_nonempty_basis_of_basis_baseChange
-- name    : GlobalTheory.nonempty_basis_of_basis_baseChange
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:12:13.133614+00:00
-- url     : https://prove2.me/theorems/24a7fdd6-bb89-4db5-b19b-8ee8511301e3
-- title:
--   Global Theory: nonempty basis of basis base Change
-- statement:
--   The Global Theory construction uses the nonempty basis of basis base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpanEqTopOfFinrankFibreEq.lean#L27-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpanEqTopOfFinrankFibreEq.lean#L27-L128

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

theorem GlobalTheory.nonempty_basis_of_basis_baseChange {B A M : Type*} [CommRing B] [CommRing A]
    [Finite (MaximalSpectrum B)] [Algebra B A] [Algebra.IsIntegral B A] [AddCommGroup M]
    [Module B M] [Module.Finite B M] {r : ℕ}
    (hinj : Function.Injective (algebraMap B A)) (b : Basis (Fin r) A (A ⊗[B] M)) :
    Nonempty (Basis (Fin r) B M) := by sorry
