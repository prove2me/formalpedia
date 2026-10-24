-- Prove2me | Theorems.Thm_K24_Global_FlatTorus_scalarSharpnessIngredient
-- name    : K24.Global.FlatTorus.scalarSharpnessIngredient
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T18:59:44.79443+00:00
-- url     : https://prove2.me/theorems/89535d51-3d49-4eef-a6dc-e15ff2cc1cb7
-- title:
--   K24: scalar oscillation estimates and the nondecaying defect witness
-- statement:
--   For every canonical Hölder exponent α, with `0 < α < 1`, let
--
--   `f_n(r) = n^(-(3+α)) sin(nr)` for `n : ℕ`,
--
--   using exactly `FlatTorus.liftedOscillation`. For a scalar function on ℝ, its
--   canonical `coordinateHolderENorm k α Set.univ` is the sum of the suprema of
--   the norms of its actual derivatives of orders 0 through k, plus the α-Hölder
--   seminorm of its kth derivative. The theorem proves the following conjunction.
--
--   1. For every natural n and every `x : FourSpace`, the actual torus scalar
--      pulled back by the prescribed periodic map equals this function:
--      `oscillatingScalar α n (quotientMap x) = f_n(x 0)`.
--   2. For every natural n, `f_n` is smooth on all of ℝ, has finite canonical
--      full order-two and order-three Hölder norms, and its order-three extended
--      norm is at most 6. The zero-index function is identically zero.
--   3. For every n>0, its order-two extended norm is at most
--      `ENNReal.ofReal (5/n)`. The real value of that finite norm tends to zero
--      as n tends to infinity.
--   4. For n≥2 define
--      `D_n(r) = expectedDefectCoefficients α n (r • basisVector 0) 0`.
--      The precise derivative difference quotient
--      `Q_n = |D_n'(0) - D_n'(π/n)| / |0 - π/n|^α`
--      satisfies
--      `Q_n = (1 + 2/n²) π^(-α) ≥ π^(-α)`.
--   5. There is no real constant K such that, for every n≥2,
--      `Q_n ≤ K * (coordinateHolderENorm 2 α Set.univ f_n).toReal`.
--      K is quantified over all real numbers; no positivity assumption on K is
--      needed for this nonexistence conclusion.
--
--   The result is a scalar analytic ingredient. The norm here is on ℝ. The theorem
--   does not establish the actual torus section norm bounds, smooth torus atlas,
--   frame/coframe identities, metric positivity, circle-action/Haar properties,
--   test-vector norm properties, or equality of the actual geometric operator
--   defect with `expectedDefectCoefficients`. Transporting the scalar estimates
--   and witness through those identifications remains necessary for the original
--   torus sharpness statement, and the full four-conjunct K24 root remains open.
--
--   Supporting the original full target https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §5.1 equations (5.6)–(5.8), using the actual diagonal perturbation and cosine test vector.

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Topology
open scoped NNReal ENNReal ContDiff

open K24.Global K24.Global.FlatTorus

theorem K24.Global.FlatTorus.scalarSharpnessIngredient :
  ∀ alpha : HolderExponent,
    (∀ (n : ℕ) (x : FourSpace),
      oscillatingScalar alpha.value n (quotientMap x) =
        liftedOscillation alpha.value n (x 0)) ∧
    (∀ n : ℕ,
      ContDiff ℝ ∞ (liftedOscillation alpha.value n) ∧
      BigHolderOn 2 alpha.value Set.univ (liftedOscillation alpha.value n) ∧
      BigHolderOn 3 alpha.value Set.univ (liftedOscillation alpha.value n) ∧
      coordinateHolderENorm 3 alpha.value Set.univ (liftedOscillation alpha.value n) ≤ 6) ∧
    (∀ n : ℕ, 0 < n →
      coordinateHolderENorm 2 alpha.value Set.univ (liftedOscillation alpha.value n) ≤
        ENNReal.ofReal (5 / (n : ℝ))) ∧
    Tendsto (fun n : ℕ =>
      (coordinateHolderENorm 2 alpha.value Set.univ (liftedOscillation alpha.value n)).toReal)
      atTop (𝓝 0) ∧
    (∀ n : ℕ, 2 ≤ n →
      let D := fun r : ℝ =>
        expectedDefectCoefficients alpha.value n (r • basisVector 0) 0
      let Q := |deriv D 0 - deriv D (Real.pi / n)| /
        Real.rpow |(0 : ℝ) - Real.pi / n| (alpha.value : ℝ)
      Q = (1 + 2 / (n : ℝ)^2) * Real.rpow Real.pi (-(alpha.value : ℝ)) ∧
      Real.rpow Real.pi (-(alpha.value : ℝ)) ≤ Q) ∧
    ¬ (∃ K : ℝ, ∀ n : ℕ, 2 ≤ n →
      let D := fun r : ℝ =>
        expectedDefectCoefficients alpha.value n (r • basisVector 0) 0
      |deriv D 0 - deriv D (Real.pi / n)| /
        Real.rpow |(0 : ℝ) - Real.pi / n| (alpha.value : ℝ) ≤
      K * (coordinateHolderENorm 2 alpha.value Set.univ
        (liftedOscillation alpha.value n)).toReal) := by sorry
