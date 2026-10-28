-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_volume_image_eq_zero_of_lipschitzOnWith_readable
-- name    : FunctionalInequalities.Analysis.volume_image_eq_zero_of_lipschitzOnWith_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:19.96919+00:00
-- url     : https://prove2.me/theorems/8a4d8199-7054-4a1a-80c4-a1a7ccc9eadf
-- title:
--   Lipschitz Images of Lebesgue Null Sets
-- statement:
--   This is an equidimensional measure-theoretic lemma.
--
--   Let $E$ be a finite-dimensional real inner-product space equipped with its measurable and Borel structures. Let $f:E\to E$, let $K\in[0,\infty)$ (`NNReal`), and let $s\subseteq E$. Assume:
--
--   1. $f$ is Lipschitz on $s$ with constant $K$.
--   2. The Lebesgue measure of $s$ is zero:
--      $$\operatorname{vol}(s)=0.$$
--
--   Then the image is also Lebesgue-null:
--
--   $$\operatorname{vol}(f(s))=0.$$
--
--   The declaration `volume_image_eq_zero_of_lipschitzOnWith_readable` does not require measurability of $s$ as an explicit hypothesis. It is restricted to maps from a finite-dimensional space to itself.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem volume_image_eq_zero_of_lipschitzOnWith {E : Type*} [NormedAddCommGroup E]
--       [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       {f : E → E} {K : NNReal} {s : Set E} (hf : LipschitzOnWith K f s)
--       (hs : (volume : Measure E) s = 0) : (volume : Measure E) (f '' s) = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Sard/Equidimensional`](https://prove2.me/theorems/80d2be47-45ea-475d-bc64-280cf904a801).
--
--   [Source excerpt, lines 133–136](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Sard/Equidimensional.lean#L133-L136) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Sard/Equidimensional.lean#L129-L147 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Sard.Equidimensional`, declaration `FunctionalInequalities.Analysis.volume_image_eq_zero_of_lipschitzOnWith`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Sard_Equidimensional

open MeasureTheory Set

theorem FunctionalInequalities.Analysis.volume_image_eq_zero_of_lipschitzOnWith_readable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → E} {K : NNReal} {s : Set E} (hf : LipschitzOnWith K f s)
    (hs : (volume : Measure E) s = 0) : (volume : Measure E) (f '' s) = 0 := by sorry
