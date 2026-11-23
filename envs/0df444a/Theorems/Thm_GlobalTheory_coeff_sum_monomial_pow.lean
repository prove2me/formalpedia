-- Prove2me | Theorems.Thm_GlobalTheory_coeff_sum_monomial_pow
-- name    : GlobalTheory.coeff_sum_monomial_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:04.898733+00:00
-- url     : https://prove2.me/theorems/a3863ff7-747d-4fe8-8f13-20085360c1d8
-- title:
--   Global Theory: coeff sum monomial pow
-- statement:
--   The Global Theory construction uses the coeff sum monomial pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FewRootsSmallDisc.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FewRootsSmallDisc.lean#L15-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditivePolyTaylorCoeffSubNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FewRootsSmallDisc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Classical
open GlobalTheory

theorem GlobalTheory.coeff_sum_monomial_pow (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (k : ℕ)
    (hk : k ≤ E) :
    (∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff (l ^ k) = a k := by sorry
