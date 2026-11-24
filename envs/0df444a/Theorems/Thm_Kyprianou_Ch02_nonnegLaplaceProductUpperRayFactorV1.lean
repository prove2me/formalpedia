-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegLaplaceProductUpperRayFactorV1
-- name    : Kyprianou.Ch02.nonnegLaplaceProductUpperRayFactorV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T02:40:42.502076+00:00
-- url     : https://prove2.me/theorems/3b33c8cd-355d-46c9-96a9-87f939843759
-- title:
--   Joint Laplace product gives upper-ray Laplace factors
-- statement:
--   Let $A$ and $B$ be pointwise nonnegative measurable real random variables on a probability space. Suppose their joint Laplace transform factors as a product of the marginal Laplace transforms at every pair of strictly positive rates. Then for every nonnegative upper threshold $a$ and every positive Laplace rate $\beta$, the restricted ENNReal Laplace integral of $B$ on the upper ray $\{A>a\}$ factors as the product of the ray probability and the unrestricted ENNReal Laplace integral of $B$. This is the upper-ray hypothesis of the Avram nonnegative independence criterion, obtained by Esscher tilting $P$ by $e^{-\beta B}$ and applying scalar Laplace uniqueness to the law of $A$.
-- source:
--   Kyprianou, Introductory Lectures on Fluctuations of Lévy Processes, Ch.2 Exercise 2.8 / Jordan–Laplace independence route; AvramDividend upper-ray Laplace criterion

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegLaplaceProductUpperRayFactorV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → ℝ) (hmA : Measurable A) (hmB : Measurable B)
    (hnA : ∀ ω, 0 ≤ A ω) (hnB : ∀ ω, 0 ≤ B ω)
    (h : ∀ u v : ℝ, 0 < u → 0 < v →
      (∫ ω, Real.exp (-(u*A ω+v*B ω)) ∂P) =
      (∫ ω, Real.exp (-(u*A ω)) ∂P)*(∫ ω, Real.exp (-(v*B ω)) ∂P))
    (a β : ℝ) (ha : 0 ≤ a) (hβ : 0 < β) :
    (∫⁻ ω in A ⁻¹' Set.Ioi a,
        ENNReal.ofReal (Real.exp (-(β * B ω))) ∂P) =
      P (A ⁻¹' Set.Ioi a) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp (-(β * B ω))) ∂P) := by sorry
