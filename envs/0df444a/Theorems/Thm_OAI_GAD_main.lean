-- Prove2me | Theorems.Thm_OAI_GAD_main
-- name    : OAI.GAD.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:41.844853+00:00
-- url     : https://prove2.me/theorems/c4b758e9-2fc8-47c1-bc09-760760a07f8e
-- statement:
--   The theorem states that, for noise parameters γ and ν both in [0,1], the generalized amplitude-damping channel (memoryless n-fold, built from tensor products of four single-site Kraus operators) satisfies four conclusions. First, its n-use Holevo quantity holevo(γ,ν,n), the supremum over all finite ensembles of n-qubit states, with no product or purity restriction, of [S(Σ wₐ N(ρₐ)) − Σ wₐ S(N(ρₐ))]/log 2 where S is von Neumann entropy and N the n-fold channel, is additive: holevo(n) = n·holevo(1) for every n ≥ 1. Second, there exists p that maximizes over [0,1] the single-parameter objective(γ,ν,q) = h((1−γ)q+γν) − g(v(q)), where h is the binary entropy, v(q)=γν(1−ν)+γ(1−γ)(q−ν)², and g(u)=h((1+√(1−4u))/2), and for every n ≥ 1 one has holevo(n) = (n/log 2)·objective(γ,ν,p). Third, the operational unassisted classical capacity, defined as the supremum of achievable rates of codes with arbitrary encodings of n-qubit states and a collective POVM decoder and with average error tending to 0, but no entanglement assistance or feedback, equals the one-shot value: capacity(γ,ν) = holevo(γ,ν,1). Fourth, for every maximizer p of the objective and every n ≥ 1, each of the 2ⁿ product phase signals, whose single-site pure state has amplitudes (√(1−p), ±√p) with the sign chosen by the bit s_k, is a valid density matrix, and holevo(n) equals phaseValue(γ,ν,p,n), the Holevo value of the equiprobable ensemble of these 2ⁿ signals. The theorem is stated with its proof admitted (sorry).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/AmplitudeDamping.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/AmplitudeDamping.lean; bytes 4308..4843
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_AmplitudeDamping

namespace OAI

universe u

noncomputable section

open scoped BigOperators ComplexOrder

open Matrix Filter

namespace GAD

theorem main (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hν : ν ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n : ℝ) * holevo γ ν 1) ∧
    (∃ p : ℝ, Maximizes γ ν p ∧
      ∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n : ℝ) / Real.log 2 * objective γ ν p) ∧
    capacity γ ν = holevo γ ν 1 ∧
    (∀ p : ℝ, Maximizes γ ν p → ∀ n : ℕ, 1 ≤ n →
      (∀ s : Basis n, IsState (phaseState p s)) ∧
      holevo γ ν n = phaseValue γ ν p n) := by
  sorry

end GAD
end
end OAI
