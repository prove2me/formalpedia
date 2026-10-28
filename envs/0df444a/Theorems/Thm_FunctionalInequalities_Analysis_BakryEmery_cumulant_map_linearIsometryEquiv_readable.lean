-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_map_linearIsometryEquiv_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.cumulant_map_linearIsometryEquiv_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:02.123347+00:00
-- url     : https://prove2.me/theorems/2c6f9c5b-4b75-4b42-9954-60d10b0a3552
-- title:
--   Cumulant Invariance Under Linear Isometries
-- statement:
--   This is the invariance of cumulants under a linear isometric equivalence.
--
--   Let $E$ and $F$ be complete finite-dimensional real inner-product spaces with Borel structures. Let $\varphi:E\to F$ be a linear isometry equivalence, let $\nu$ be any measure on $E$, let $k\in\mathbb N$, and let $u:\mathrm{Fin}(k)\to E$. Then
--
--   $$
--   \kappa_k^{\varphi_\#\nu}
--   \bigl(\varphi u_1,\ldots,\varphi u_k\bigr)
--   =
--   \kappa_k^\nu(u_1,\ldots,u_k).
--   $$
--
--   The pushforward is `ν.map φ`. No finiteness, nonzero, or exponential-moment assumption appears in the theorem type. This provides a reusable coordinate-invariance property for cumulant tensors.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cumulant_map_linearIsometryEquiv [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
--       [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
--       [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
--       (φ : E ≃ₗᵢ[ℝ] F) (ν : Measure E) (k : ℕ) (u : Fin k → E) :
--       cumulant (ν.map φ) k (fun i => φ (u i)) = cumulant ν k u
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Previous: [`contDiffOn_logLaplace_ball`](https://prove2.me/theorems/dd1e2494-e9a9-46a2-a434-95c8dca4c3ef) · Next: [`cumulant_map_affine`](https://prove2.me/theorems/ff092742-6b2a-4aa9-b96d-052edb49e94b).
--
--   [Source excerpt, lines 813–817](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L813-L817) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L811-L855 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.cumulant_map_linearIsometryEquiv`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

open MeasureTheory
universe u
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.cumulant_map_linearIsometryEquiv_readable [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (φ : E ≃ₗᵢ[ℝ] F) (ν : Measure E) (k : ℕ) (u : Fin k → E) :
    cumulant (ν.map φ) k (fun i => φ (u i)) = cumulant ν k u := by sorry
