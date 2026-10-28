-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_expTilt_tilted_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.expTilt_tilted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:02.150794+00:00
-- url     : https://prove2.me/theorems/b77ce921-0d7b-4b31-ac8b-28afb215f4d2
-- title:
--   Composition Rule for Exponential Tilts
-- statement:
--   This theorem relates an exponential tilt of a tilted measure to a single tilt with a modified potential.
--
--   Let $E$ be a real inner-product space, let $m$ be a measure on $E$, and let $V:E\to\mathbb R$. Assume that $x\mapsto e^{-V(x)}$ is integrable with respect to $m$. For every $z\in E$,
--
--   $$\operatorname{expTilt}\bigl(m.\operatorname{tilted}(-V)\bigr)(z)
--   =m.\operatorname{tilted}\bigl(-(V-\langle z,\cdot\rangle)\bigr).$$
--
--   The definitions `expTilt` and `Measure.tilted` are used exactly as stated; no finite-dimensional, completeness, Borel, or Haar-measure assumptions are required by the theorem. This identity is a basic algebraic rule for manipulating exponential tilts.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem expTilt_tilted {V : E → ℝ} (hV : Integrable (fun x => Real.exp ((-V) x)) m) (z : E) :
--       expTilt (m.tilted (-V)) z = m.tilted (-fun y => V y - ⟪z, y⟫)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Previous: [`gradient_sub_inner`](https://prove2.me/theorems/6e39480b-596b-4064-876c-d786d322b2b9) · Next: [`integrable_gradient_expTilt`](https://prove2.me/theorems/4ce78d47-f6fb-43d4-9cf4-e4a847a5b302).
--
--   [Source excerpt, lines 91–92](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean#L91-L92) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean#L89-L104 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.expTilt_tilted`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic

open MeasureTheory FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.expTilt_tilted_readable {V : E → ℝ} (hV : Integrable (fun x => Real.exp ((-V) x)) m) (z : E) :
    expTilt (m.tilted (-V)) z = m.tilted (-fun y => V y - ⟪z, y⟫) := by sorry
