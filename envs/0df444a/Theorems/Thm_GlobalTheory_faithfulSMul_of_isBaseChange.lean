-- Prove2me | Theorems.Thm_GlobalTheory_faithfulSMul_of_isBaseChange
-- name    : GlobalTheory.faithfulSMul_of_isBaseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:28:47.695005+00:00
-- url     : https://prove2.me/theorems/998d3a20-5327-49e8-8264-698143dcde5d
-- title:
--   Global Theory: faithful SMul of is Base Change
-- statement:
--   The Global Theory construction uses the faithful SMul of is Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L321-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L321-L331

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (G : Type*) [Group G]
variable {R S A A' : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing A']
  [Algebra R S] [Algebra R A] [Algebra R A'] [Algebra S A'] [IsScalarTower R S A']
  [MulSemiringAction G A] [SMulCommClass G R A] [MulSemiringAction G A'] [SMulCommClass G S A']
omit [MulSemiringAction G A] [SMulCommClass G R A] [MulSemiringAction G A']
  [SMulCommClass G S A']

theorem GlobalTheory.faithfulSMul_of_isBaseChange [Module.Flat R S] [FaithfulSMul R A]
    (f : A →ₐ[R] A') (hb : IsBaseChange S f.toLinearMap) : FaithfulSMul S A' := by sorry
