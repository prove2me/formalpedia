-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_finite_quot_span_of_ne_zero
-- name    : GlobalTheory.UnitLemma.finite_quot_span_of_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:37:59.931804+00:00
-- url     : https://prove2.me/theorems/e964a9cb-009f-4c99-9096-38d329eda46c
-- title:
--   Unit Lemma: finite quot span of ne zero
-- statement:
--   The Unit Lemma construction uses the finite quot span of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSubmodulesBetweenMulLeftImageLattice.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSubmodulesBetweenMulLeftImageLattice.lean#L7-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenMulLeftImageLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.finite_quot_span_of_ne_zero (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (c : O) (hc : c ≠ 0) : Finite (O ⧸ Ideal.span {c}) := by sorry
