-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cutoff_eq_one_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.cutoff_eq_one_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:04.985251+00:00
-- url     : https://prove2.me/theorems/85395b56-b174-481f-86b1-0d68ab4624ec
-- title:
--   Cutoff Equals One Inside Its Radius
-- statement:
--   This is a basic property of the scaled smooth cutoff.
--
--   Let $E$ be a real inner-product space, let $R>0$, and let $x\in E$ satisfy $\|x\|\leq R$. Then
--
--   $$
--   \operatorname{cutoff}_R(x)=1.
--   $$
--
--   The function `cutoff R` is the unit bump evaluated at $R^{-1}x$. No completeness, finite-dimensionality, or measurable-space assumptions are required. This fact is used when removing compact-support restrictions by cutoff approximation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
--   theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : cutoff R x = 1
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/Temperate`](https://prove2.me/theorems/2dcac3f7-3919-472b-8b13-591e955577ca).
--
--   Previous: [`hasCompactSupport_cutoff`](https://prove2.me/theorems/d329d169-7e19-4110-aeb8-20df20dddcfb) · Next: [`norm_iteratedFDeriv_cutoff_le`](https://prove2.me/theorems/d1de012f-6a55-4617-aaf5-23eabb181c3e).
--
--   [Source excerpt, lines 77–78](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L77-L78) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L77-L93 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.cutoff_eq_one`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.cutoff_eq_one_readable {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : cutoff R x = 1 := by sorry
