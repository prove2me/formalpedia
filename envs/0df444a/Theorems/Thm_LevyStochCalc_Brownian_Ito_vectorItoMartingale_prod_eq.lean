-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_vectorItoMartingale_prod_eq
-- name    : LevyStochCalc.Brownian.Ito.vectorItoMartingale_prod_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:43:23.344174+00:00
-- url     : https://prove2.me/theorems/6f32972f-b76b-44c9-ab55-552dce6c199e
-- title:
--   vectorItoMartingale prod eq
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.vectorItoMartingale_prod_eq` is extracted from `LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoQuadVarRiemannDecomposition_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Decomposition and convergence of the quadratic-variation Riemann sum

The product of the increments of two coordinates of a continuous vector Itô process splits into a
drift–drift term, two drift–martingale terms and the product of the increments of the martingale
parts, and the last splits further into the compensated products on the diagonal in the Brownian
index, their compensators, and the cross terms off that diagonal. Weighting the products by a
bounded continuous function of the process frozen at the left endpoint of each cell of a uniform
grid, the five error terms are `O(m^{-1/2})` in `L¹` and the sixth group is a frozen-weight
Riemann sum for `∫_0^T φ(X_s)·(∑ₖ H^{p,k}_s H^{q,k}_s) ds`, so the weighted Riemann sum converges
in `L¹` to that integral at rate `√(T/m)`.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.prod_sub_ae` — the product of the increments of
  two coordinates.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.quadVarRiemann_decomp_ae` — the decomposition of
  the weighted product sum into six groups.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le` — the `L¹`
  rate of convergence of the weighted quadratic-variation Riemann sum.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section VectorQuadVar

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.vectorItoMartingale_prod_eq (p q : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (ω : Ω) :
    (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
      * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
      = (∑ k : Fin d, polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω)
        + (∑ k : Fin d, ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
        + ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
            crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l u v ω := by sorry
