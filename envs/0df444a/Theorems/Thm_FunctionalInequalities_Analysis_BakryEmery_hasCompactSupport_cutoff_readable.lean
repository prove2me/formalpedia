-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_hasCompactSupport_cutoff_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_cutoff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:59.980416+00:00
-- url     : https://prove2.me/theorems/d329d169-7e19-4110-aeb8-20df20dddcfb
-- title:
--   Compact Support of the Scaled Cutoff
-- statement:
--   This technical lemma establishes compact support for the scaled cutoff function.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $R>0$. For the function `cutoff R`, defined by scaling the fixed unit bump, one has
--
--   $$\operatorname{HasCompactSupport}(\operatorname{cutoff}(R)).$$
--
--   More specifically, the support is contained in the closed ball of radius $2R$. This fact is used to construct compactly supported approximations and cutoff test functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
--   theorem hasCompactSupport_cutoff {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutoff (E := E) R)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/Temperate`](https://prove2.me/theorems/2dcac3f7-3919-472b-8b13-591e955577ca).
--
--   Next: [`cutoff_eq_one`](https://prove2.me/theorems/85395b56-b174-481f-86b1-0d68ab4624ec).
--
--   [Source excerpt, lines 43–44](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L43-L44) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L43-L75 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_cutoff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_cutoff_readable {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutoff (E := E) R) := by sorry
