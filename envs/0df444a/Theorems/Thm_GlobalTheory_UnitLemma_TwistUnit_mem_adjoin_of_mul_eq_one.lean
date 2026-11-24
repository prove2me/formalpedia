-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_TwistUnit_mem_adjoin_of_mul_eq_one
-- name    : GlobalTheory.UnitLemma.TwistUnit.mem_adjoin_of_mul_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:17.299219+00:00
-- url     : https://prove2.me/theorems/3f332b44-c606-48ab-af4d-28373b9c151a
-- title:
--   Twist Unit: mem adjoin of mul eq one
-- statement:
--   The Twist Unit construction uses the mem adjoin of mul eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemAdjoinOfMulEqOne.lean#L9-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemAdjoinOfMulEqOne.lean#L9-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigmaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemAdjoinOfMulEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TwistUnit
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.UnitLemma.TwistUnit.mem_adjoin_of_mul_eq_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s t : A}
    (h : s * t = 1) (ht : IsIntegral O t) : t ∈ Algebra.adjoin O {s} := by sorry
