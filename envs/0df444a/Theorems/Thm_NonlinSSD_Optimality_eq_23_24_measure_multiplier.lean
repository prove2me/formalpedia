-- Prove2me | Theorems.Thm_NonlinSSD_Optimality_eq_23_24_measure_multiplier
-- name    : NonlinSSD.Optimality.eq_23_24_measure_multiplier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:00:22.921171+00:00
-- url     : https://prove2.me/theorems/688fcf6d-478d-44bd-81f3-c8fa0afbfcae
-- title:
--   Eqs. (23)–(24) — existence of a nonnegative measure multiplier
-- statement:
--   Consider the split program (11)–(14), assume uniform dominance, and let $(\hat z,\hat X)$ be an optimal solution. There are finite nonnegative measures $\hat\mu_i$ supported on $[a_i,b_i]$ such that, for $C=\{(z,X):z\in Z,\ X_i\in\mathcal L^1,\ X_i\le G_i(z)\text{ almost surely}\}$,
--   $$\Lambda(\hat z,\hat X,\hat\mu)=\max_{(z,X)\in C}\Lambda(z,X,\hat\mu),\qquad \int_{[a_i,b_i]}[F_2(Y_i;\eta)-F_2(\hat X_i;\eta)]\,d\hat\mu_i(\eta)=0\quad(1\le i\le m).$$
--
--   This is the measure multiplier stage of the proof of Theorem 2; the measures are subsequently converted to utility functions.
--
--   **Formalization Note** The measures are extended by zero off their intervals, and their finiteness is explicit. The maximum means that the feasible pair belongs to $C$ and bounds every competitor's Lagrangian value. Integrability comes from the problem data and the quantified class of $X$.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 8, Eqs. (23)–(24), proof of Theorem 2

import Mathlib
import Definitions.Def_NonlinSSD_Optimality_Basic

namespace NonlinSSD.Optimality

open MeasureTheory

/-- Eqs. (23)–(24), p. 8: a nonnegative measure multiplier attains the maximum of
the measure Lagrangian on `C` and annihilates every dominance slack. -/
theorem eq_23_24_measure_multiplier
    {Ω 𝒵 : Type*} [MeasurableSpace Ω]
    [AddCommGroup 𝒵] [Module ℝ 𝒵] [TopologicalSpace 𝒵]
    [IsTopologicalAddGroup 𝒵] [ContinuousSMul ℝ 𝒵]
    [LocallyConvexSpace ℝ 𝒵] [T2Space 𝒵]
    [TopologicalSpace.SeparableSpace 𝒵]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}
    (pr : Problem Ω 𝒵 P m) (z : 𝒵) (X : Fin m → Ω → ℝ)
    (hdom : pr.UniformDominance) (hopt : pr.IsOptimal z X) :
    ∃ μ : Fin m → Measure ℝ,
      (∀ i, μ i Set.univ < ⊤) ∧
      (∀ i, μ i (Set.Icc (pr.a i) (pr.b i))ᶜ = 0) ∧
      pr.InC z X ∧
      (∀ z' X', pr.InC z' X' →
        pr.Lambda z' X' μ ≤ pr.Lambda z X μ) ∧
      ∀ i, (∫ η in Set.Icc (pr.a i) (pr.b i),
        (F2 P (pr.Y i) η - F2 P (X i) η) ∂μ i) = 0 := by sorry

end NonlinSSD.Optimality
