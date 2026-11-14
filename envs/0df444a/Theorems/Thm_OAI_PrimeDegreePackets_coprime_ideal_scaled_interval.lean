-- Prove2me | Theorems.Thm_OAI_PrimeDegreePackets_coprime_ideal_scaled_interval
-- name    : OAI.PrimeDegreePackets.coprime_ideal_scaled_interval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:32:23.066792+00:00
-- url     : https://prove2.me/theorems/54491c67-14c5-4fd9-8612-89021d0f608e
-- title:
--   OAI.PrimeDegreePackets.coprime_ideal_scaled_interval: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PrimeDegreePackets.coprime_ideal_scaled_interval` of [lean/OAI/NumberTheory/PrimePackets/LocalEuler.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/LocalEuler.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PrimeDegreePackets`, with `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal`, `open MeasureTheory Filter Set Module`, `open scoped TensorProduct`, `open Set Module`, `open MeasureTheory Set`, `open scoped ENNReal`, `open IsDiscreteValuationRing IsLocalRing`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set IsDiscreteValuationRing`, `open Filter`, `open scoped BigOperators Topology`, `open NumberField`, `open scoped NumberField nonZeroDivisors`, `open scoped BigOperators ArithmeticFunction.zeta`, `open Finset`, `open scoped BigOperators Classical ArithmeticFunction.Moebius`, `open Finset Nat ArithmeticFunction BoundingSieve`, `open scoped BigOperators Classical`, `open Finset Nat`, `open scoped BigOperators`, `open Filter Topology`, `open scoped nonZeroDivisors`, `open Ideal NumberField Finset UniqueFactorizationMonoid`, `open NumberField Finset`, `open scoped BigOperators ENNReal nonZeroDivisors`):
--
--   ```lean
--   theorem coprime_ideal_scaled_interval (n : ℕ) :
--       ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ R : ℕ,
--         ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℤ (𝓞 K) = n →
--           ∀ q a b d : ℕ, 0 < q → 0 < d → Real.log q ≤ (b/d : ℕ) →
--             R ≤ b/d → a ≤ b → η*(b/d : ℕ) ≤ (b/d : ℕ)-(a/d : ℕ) →
--             b ≤ (b/d)^2 →
--             ((b/d : ℕ):ℝ)-(a/d : ℕ) ≤ 2*((b:ℝ)-a)/d →
--             (∑ m ∈ Ioc (a/d) (b/d), coprimeIdealCoefficient K q m) ≤
--               C * (((b:ℝ)-a)/d) *
--                 ((NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b) /
--                   badPrimeEuler K q
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.badPrimeEuler` and `OAI.PrimeDegreePackets.coprimeIdealCoefficient` (definitions bundle `OAIQ244Duke012` of this split).
--
--   **Used by.** The proof of `OAI.PrimeDegreePackets.weightedIdeal_small_norm_bound` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/LocalEuler.lean (declaration OAI.PrimeDegreePackets.coprime_ideal_scaled_interval)

import Mathlib
import Definitions.Def_OAIQ244Duke012

section

attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid

namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors

theorem coprime_ideal_scaled_interval (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ R : ℕ,
      ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℤ (𝓞 K) = n →
        ∀ q a b d : ℕ, 0 < q → 0 < d → Real.log q ≤ (b/d : ℕ) →
          R ≤ b/d → a ≤ b → η*(b/d : ℕ) ≤ (b/d : ℕ)-(a/d : ℕ) →
          b ≤ (b/d)^2 →
          ((b/d : ℕ):ℝ)-(a/d : ℕ) ≤ 2*((b:ℝ)-a)/d →
          (∑ m ∈ Ioc (a/d) (b/d), coprimeIdealCoefficient K q m) ≤
            C * (((b:ℝ)-a)/d) *
              ((NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b) /
                badPrimeEuler K q := by
  sorry

end PrimeDegreePackets
end
end

end OAI
end
