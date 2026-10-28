-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_map_affine_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.cumulant_map_affine_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:59.962037+00:00
-- url     : https://prove2.me/theorems/ff092742-6b2a-4aa9-b96d-052edb49e94b
-- title:
--   Cumulant Transformation Under Affine Maps
-- statement:
--   This formalizes the affine transformation rule for cumulants, corresponding to Bizeul–Klartag–Lehec, Equation (77), p. 19.
--
--   Let $E$ and $F$ be complete finite-dimensional real inner-product spaces with Borel structures. Let $T:E\to F$ be a continuous linear equivalence, let $a\in E$, and let $\mu$ be a finite nonzero measure on $E$. Assume all exponential norm moments of $\mu$ are finite. For $k\geq2$ and directions $u_i\in F$,
--
--   $$
--   \kappa_k^{(T(\cdot-a))_\#\mu}(u_1,\ldots,u_k)
--   =
--   \kappa_k^\mu(T^*u_1,\ldots,T^*u_k).
--   $$
--
--   The pushforward is `Measure.map (fun x => T (x - a)) μ`, and $T^*$ is represented by `ContinuousLinearMap.adjoint`. The translation does not affect cumulants of order at least two.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cumulant_map_affine [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
--       [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
--       [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
--       (T : E ≃L[ℝ] F) (a : E) (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
--       {k : ℕ} (hk : 2 ≤ k) (u : Fin k → F) :
--       cumulant (μ.map (fun x => T (x - a))) k u =
--         cumulant μ k (fun i => ContinuousLinearMap.adjoint (T : E →L[ℝ] F) (u i))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Previous: [`cumulant_map_linearIsometryEquiv`](https://prove2.me/theorems/2c6f9c5b-4b75-4b42-9954-60d10b0a3552) · Next: [`letwinQuadraticBound_of_tendsto_moments`](https://prove2.me/theorems/6ecfa844-3974-41e9-92f3-a8a463c1d859).
--
--   [Source excerpt, lines 888–895](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L888-L895) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L885-L975 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.cumulant_map_affine`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

open MeasureTheory
universe u
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.cumulant_map_affine_readable [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (T : E ≃L[ℝ] F) (a : E) (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {k : ℕ} (hk : 2 ≤ k) (u : Fin k → F) :
    cumulant (μ.map (fun x => T (x - a))) k u =
      cumulant μ k (fun i => ContinuousLinearMap.adjoint (T : E →L[ℝ] F) (u i)) := by sorry
