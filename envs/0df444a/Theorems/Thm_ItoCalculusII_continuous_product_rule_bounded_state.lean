-- Prove2me | Theorems.Thm_ItoCalculusII_continuous_product_rule_bounded_state
-- name    : ItoCalculusII.continuous_product_rule_bounded_state
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:25:18.889225+00:00
-- url     : https://prove2.me/theorems/ba76f72c-4731-4147-82f8-ab50fce67ab8
-- title:
--   Itô Product Rule for a Deterministically Bounded Two-Coordinate State
-- statement:
--   For a two-coordinate continuous adapted Itô version driven by finitely many Brownian coordinates, assume bounded drift and diffusion, finite square energy for all required coefficients and cross terms, and a deterministic bound on both state coordinates throughout a positive time horizon. Assume the combined product-rule Brownian integrands exist, are measurable and progressive, and have finite energy. Prove the fixed-time almost-sure product formula with drift terms, the sum of coordinate quadratic-covariation densities, and the Brownian integrals of YH_X+XH_Y. The equality is not among the hypotheses.
-- source:
--   Classical stochastic product rule, derived by applying the accepted finite-dimensional Prove2Me vector Itô theorem 9fc109b4-701c-4220-bf8e-2dcb0c672023 to a compactly supported product and simplifying its mixed Hessian. Related accepted cutoff and Hessian references are recorded in this captain proposal.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoVersionExists
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal

universe u

/-- Product formula for two continuous coordinates of a Brownian vector Itô process.
The stochastic product identity is the conclusion, not an assumption. -/

theorem ItoCalculusII.continuous_product_rule_bounded_state
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    (H : Fin 2 → Fin d → Ω → ℝ → ℝ)
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin 2) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (X₀ : Ω → Fin 2 → ℝ)
    (bdrift : Fin 2 → Ω → ℝ → ℝ)
    (X : ℝ → Ω → Fin 2 → ℝ)
    (hX : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀m : ∀ p : Fin 2, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p : Fin 2, Measurable (Function.uncurry (bdrift p)))
    {B C : ℝ} (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hB : ∀ p ω s, |bdrift p ω s| ≤ B)
    (hCH : ∀ p k ω s, |H p k ω s| ≤ C)
    (hplusm : ∀ p q k, Measurable (Function.uncurry
      fun ω s => H p k ω s + H q k ω s))
    (hplusp : ∀ p q k, Probability.ProgressivelyMeasurable ℱ
      (fun ω s => H p k ω s + H q k ω s))
    (hplusq : ∀ (p q : Fin 2) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hJm : ∀ k : Fin d, Measurable (Function.uncurry
      fun ω s => X s ω 1 * H 0 k ω s + X s ω 0 * H 1 k ω s))
    (hJp : ∀ k : Fin d, Probability.ProgressivelyMeasurable ℱ
      (fun ω s => X s ω 1 * H 0 k ω s + X s ω 0 * H 1 k ω s))
    (hJq : ∀ (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖X s ω 1 * H 0 k ω s + X s ω 0 * H 1 k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (R : ℝ) (hR : 0 < R)
    (hXR : ∀ ω s, s ∈ Set.Icc (0 : ℝ) T → ‖X s ω‖ < R) :
    (fun ω => X T ω 0 * X T ω 1 - X 0 ω 0 * X 0 ω 1) =ᵐ[P] fun ω =>
      (∫ s in Set.Ioc (0 : ℝ) T,
         (X s ω 1 * bdrift 0 ω s + X s ω 0 * bdrift 1 ω s +
           ∑ k : Fin d, H 0 k ω s * H 1 k ω s) ∂volume) +
      ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
        (fun ω s => X s ω 1 * H 0 k ω s + X s ω 0 * H 1 k ω s)
        (hJm k) (hJp k) (hJq k) T ω := by sorry
