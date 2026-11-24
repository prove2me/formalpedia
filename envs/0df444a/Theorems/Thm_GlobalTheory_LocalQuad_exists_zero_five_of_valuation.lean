-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_exists_zero_five_of_valuation
-- name    : GlobalTheory.LocalQuad.exists_zero_five_of_valuation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:58.247968+00:00
-- url     : https://prove2.me/theorems/8cae7912-90d5-4a4d-a309-b005778e3264
-- title:
--   Local Quad: exists zero five of valuation
-- statement:
--   The Local Quad construction uses the exists zero five of valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L218-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L218-L289

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open FiveVar

theorem GlobalTheory.LocalQuad.exists_zero_five_of_valuation {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (v : Valuation K ℤᵐ⁰) (hv : Function.Surjective v)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x)
    (hcw : ∀ c : Fin 3 → Fin 3 → K, (∀ i j, v (c i j) ≤ 1) →
      ∃ x : Fin 3 → K, (∀ i, v (x i) ≤ 1) ∧ (∃ i, v (x i) = 1) ∧
        v (∑ i, ∑ j, c i j * x i * x j) < 1)
    (a : Fin 5 → K) : ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by sorry
