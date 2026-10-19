-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_weight_hasDerivAt_center
-- name    : OAI.TriangularHilbert.Heat.weight_hasDerivAt_center
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:32:56.627063+00:00
-- url     : https://prove2.me/theorems/6d635e46-d87e-43bc-bab5-dc2e486bb300
-- title:
--   Derivative of a heat weight in its centre
-- statement:
--   The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$. For $\sigma>0$, the heat weight is differentiable in the centre $p$, with derivative given by the score:
--   $$
--   \frac{\partial}{\partial p}\,h\,\phi_\sigma(u-p)=\frac{u-p}\sigma\cdot h\,\phi_\sigma(u-p) .
--   $$
--
--   Moving the centre towards $u$ increases the weight at $u$ at a rate proportional to the distance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/Gaussian.lean#L37-L51

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology

theorem OAI.TriangularHilbert.Heat.weight_hasDerivAt_center (h u p σ : ℝ) (_hσ : 0 < σ) :
    HasDerivAt (fun q => weight h u q σ) (score u p σ * weight h u p σ) p := by sorry
