-- Prove2me | Theorems.Thm_GlobalTheory_IntegralOverComplete_exists_subalgebra
-- name    : GlobalTheory.IntegralOverComplete.exists_subalgebra
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:54.756125+00:00
-- url     : https://prove2.me/theorems/fac37983-0b82-48e1-bbf4-91aff08abb03
-- title:
--   Integral Over Complete: exists subalgebra
-- statement:
--   The Integral Over Complete construction uses the exists subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HenselianIUnionCompleteOfIntegralOverCompleteDvr.lean#L16-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HenselianIUnionCompleteOfIntegralOverCompleteDvr.lean#L16-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HenselianIUnionCompleteOfIntegralOverCompleteDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.IntegralOverComplete
open IsLocalRing Polynomial

theorem GlobalTheory.IntegralOverComplete.exists_subalgebra (W R : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [CharZero W] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra W R] [FaithfulSMul W R] [Algebra.IsIntegral W R]
    (s : Finset R) :
    ∃ (W' : Subalgebra W R) (_ : IsDiscreteValuationRing W'), (↑s : Set R) ⊆ W' ∧
      IsAdicComplete (maximalIdeal W') W' ∧ Module.Finite W W' ∧
      IsLocalHom W'.val.toRingHom := by sorry
