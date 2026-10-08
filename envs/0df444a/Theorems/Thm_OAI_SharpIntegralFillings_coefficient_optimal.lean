-- Prove2me | Theorems.Thm_OAI_SharpIntegralFillings_coefficient_optimal
-- name    : OAI.SharpIntegralFillings.coefficient_optimal
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:19.963989+00:00
-- url     : https://prove2.me/theorems/cd073b9f-8006-4dd8-9578-939525f971e7
-- statement:
--   The theorem states that for every integer n ≥ 2 there exists an integral n-current T in Euclidean space ℝ^{n+1}, in the metric-current sense (a multilinear functional on a bounded Lipschitz function and n Lipschitz functions satisfying linearity, continuity, locality and finite-mass axioms, whose mass is the least total mass of a finite controlling measure, and which is a countable sum of integer-multiplicity bi-Lipschitz chart pieces with disjoint images and summable masses, with an integral boundary as well), such that T has compact support, is a cycle (its boundary is zero), and has strictly positive mass, and such that every compactly supported integral (n+1)-current S in ℝ^{n+1} whose boundary equals T satisfies mass(S) ≥ c_n · mass(T)^{(n+1)/n}. Here the filling coefficient is c_n = 1/((n+1)·σ_n^{1/n}), where σ_n = (n+1)·ω_{n+1} and ω_{n+1} is the Lebesgue volume of the unit ball in ℝ^{n+1}. This asserts that the filling inequality with this constant is attained: some nonzero compactly supported integral cycle has no filling of smaller mass than the bound, so the constant cannot be improved. The theorem is admitted in the source without proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FillingCoefficient.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FillingCoefficient.lean; bytes 4812..5194
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_FillingCoefficient

namespace OAI

open Set Filter MeasureTheory

open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings

attribute [local instance] Classical.propDecidable

universe u

theorem coefficient_optimal (n : ℕ) (hn : 2 ≤ n) :
    ∃ T : IntegralCurrent (Euc (n + 1)) n,
      CompactlySupported T.val ∧ IsCycle T.val ∧ 0 < mass T.val ∧
      ∀ S : IntegralCurrent (Euc (n + 1)) (n + 1),
        CompactlySupported S.val → boundarySucc S.val = T.val →
        fillingCoefficient n * (mass T.val) ^ fillingPower n ≤ mass S.val := by
  sorry

end SharpIntegralFillings
end OAI
