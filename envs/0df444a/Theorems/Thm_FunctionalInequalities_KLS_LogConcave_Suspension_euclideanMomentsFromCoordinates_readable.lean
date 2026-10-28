-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_euclideanMomentsFromCoordinates_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.euclideanMomentsFromCoordinates_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:38.219833+00:00
-- url     : https://prove2.me/theorems/6a6a83e2-bb43-45bd-81ba-a4cf13238710
-- title:
--   Euclidean Moment Identities From Coordinate Moments
-- statement:
--   This auxiliary lemma assembles Euclidean moment identities from coordinatewise hypotheses.
--
--   Let $A$ be a measurable space, $\nu$ a probability measure on $A$, and $I$ a finite type with decidable equality. Let $Y:A\to\mathbb R^I$ be measurable, with Euclidean target `EuclideanSpace ℝ I`. Assume:
--   1. Each coordinate $Y_i$ belongs to $L^2(\nu)$ (`MemLp`).
--   2. $\int Y_i\,d\nu=0$ for every $i\in I$.
--   3. $\int Y_iY_j\,d\nu=\delta_{ij}$ for every $i,j\in I$, where $\delta_{ij}$ is $1$ if $i=j$ and $0$ otherwise.
--
--   Then
--   $$
--   Y\in L^2(\nu;\mathbb R^I),\qquad \int Y\,d\nu=0,\qquad
--   \forall u,v\in\mathbb R^I,\quad
--   \int\langle u,Y\rangle\langle v,Y\rangle\,d\nu=\langle u,v\rangle.
--   $$
--
--   This provides a finite-dimensional interface between coordinate moments and the bilinear second-moment identity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem euclideanMomentsFromCoordinates {A I : Type*} [MeasurableSpace A]
--       [Fintype I] [DecidableEq I] (ν : Measure A) [IsProbabilityMeasure ν] (Y : A → EuclideanSpace ℝ I)
--       (hY : Measurable Y) (h2 : ∀ i, MemLp (fun x => Y x i) 2 ν)
--       (h0 : ∀ i, (∫ x, Y x i ∂ν) = 0)
--       (hcov : ∀ i j, (∫ x, Y x i * Y x j ∂ν) = if i = j then 1 else 0) :
--       MemLp Y 2 ν ∧ (∫ x, Y x ∂ν) = 0 ∧
--         ∀ u v : EuclideanSpace ℝ I, (∫ x, ⟪u, Y x⟫ * ⟪v, Y x⟫ ∂ν) = ⟪u, v⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Moments`](https://prove2.me/theorems/bb78b4a9-f1ce-44b8-9c83-f67999cad00c).
--
--   Previous: [`integral_scalar_mul_inner`](https://prove2.me/theorems/dbb61a45-7681-4409-992e-00167fbe6df2) · Next: [`jointLaw_moments_of_laplace`](https://prove2.me/theorems/908317d8-6064-4b90-a2bb-84206bede78e).
--
--   [Source excerpt, lines 178–184](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Moments.lean#L178-L184) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Moments.lean#L178-L234 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Moments`, declaration `_private.FunctionalInequalities.KLS.BKL.Suspension.Moments.0.FunctionalInequalities.KLS.LogConcave.Suspension.euclideanMomentsFromCoordinates`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Moments

open MeasureTheory ProbabilityTheory FunctionalInequalities.Probability
open scoped RealInnerProductSpace

theorem FunctionalInequalities.KLS.LogConcave.Suspension.euclideanMomentsFromCoordinates_readable {A I : Type*} [MeasurableSpace A]
    [Fintype I] [DecidableEq I] (ν : Measure A) [IsProbabilityMeasure ν] (Y : A → EuclideanSpace ℝ I)
    (hY : Measurable Y) (h2 : ∀ i, MemLp (fun x => Y x i) 2 ν)
    (h0 : ∀ i, (∫ x, Y x i ∂ν) = 0)
    (hcov : ∀ i j, (∫ x, Y x i * Y x j ∂ν) = if i = j then 1 else 0) :
    MemLp Y 2 ν ∧ (∫ x, Y x ∂ν) = 0 ∧
      ∀ u v : EuclideanSpace ℝ I, (∫ x, ⟪u, Y x⟫ * ⟪v, Y x⟫ ∂ν) = ⟪u, v⟫ := by sorry
