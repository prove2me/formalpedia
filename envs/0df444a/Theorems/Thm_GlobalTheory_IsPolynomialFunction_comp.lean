-- Prove2me | Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
-- name    : GlobalTheory.IsPolynomialFunction.comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:28.334799+00:00
-- url     : https://prove2.me/theorems/e00aba51-2881-4185-a8dc-e0ae1c3e847e
-- title:
--   Is Polynomial Function: comp
-- statement:
--   The Is Polynomial Function construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L38-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable (K : Type*) [CommSemiring K] {M : Type*} [AddCommMonoid M] [Module K M]
variable {K}

theorem GlobalTheory.IsPolynomialFunction.comp {N : Type*} [AddCommMonoid N] [Module K N] {P : M → K}
    (hP : IsPolynomialFunction K P) (L : N →ₗ[K] M) : IsPolynomialFunction K (fun y => P (L y)) := by sorry
