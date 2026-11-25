-- Prove2me | Theorems.Thm_GlobalTheory_Nef_RatDilation_natDegree_eq_zero_of_sq_dvd
-- name    : GlobalTheory.Nef.RatDilation.natDegree_eq_zero_of_sq_dvd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:59.91355+00:00
-- url     : https://prove2.me/theorems/a98f602e-c2ea-4075-87a4-85e73769d8a4
-- title:
--   Rat Dilation: nat Degree eq zero of sq dvd
-- statement:
--   The Rat Dilation construction uses the nat Degree eq zero of sq dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatDegreeEqZeroOfSqDvd.lean#L28-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatDegreeEqZeroOfSqDvd.lean#L28-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeEqZeroOfSqDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
open Polynomial
open GlobalTheory.Nef.RatDilation

theorem GlobalTheory.Nef.RatDilation.natDegree_eq_zero_of_sq_dvd {F : Type} [Field F] [CharZero F] (f g : F[X]) (hf : f ≠ 0)
    (hc : IsCoprime f g) (h : f.comp (C (2:F) * X) * g ^ 2 = g.comp (C (2:F) * X) * f ^ 2) :
    f.natDegree = 0 := by sorry
