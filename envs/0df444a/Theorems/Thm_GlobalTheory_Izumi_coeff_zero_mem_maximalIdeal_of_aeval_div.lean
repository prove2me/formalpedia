-- Prove2me | Theorems.Thm_GlobalTheory_Izumi_coeff_zero_mem_maximalIdeal_of_aeval_div
-- name    : GlobalTheory.Izumi.coeff_zero_mem_maximalIdeal_of_aeval_div
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:22:12.13242+00:00
-- url     : https://prove2.me/theorems/60a9951e-e77b-4091-a6e0-b585bcd66d72
-- title:
--   Izumi: coeff zero mem maximal Ideal of aeval div
-- statement:
--   The Izumi construction uses the coeff zero mem maximal Ideal of aeval div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDominatingLocalDomainEqMulMaximal.lean#L41-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDominatingLocalDomainEqMulMaximal.lean#L41-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingLocalDomainEqMulMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.Izumi

theorem GlobalTheory.Izumi.coeff_zero_mem_maximalIdeal_of_aeval_div {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsIntegrallyClosed R] (f G : R) (h : G ∉ Ideal.span {f}) (P : R[X])
    (hP : aeval (algebraMap R (FractionRing R) f / algebraMap R (FractionRing R) G) P = 0) :
    P.coeff 0 ∈ maximalIdeal R := by sorry
