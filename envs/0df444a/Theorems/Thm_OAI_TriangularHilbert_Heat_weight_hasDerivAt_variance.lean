-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_weight_hasDerivAt_variance
-- name    : OAI.TriangularHilbert.Heat.weight_hasDerivAt_variance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:34:18.639078+00:00
-- url     : https://prove2.me/theorems/bb66bb5f-581e-4573-896d-c698c387d5f5
-- title:
--   Derivative of a heat weight in its variance
-- statement:
--   The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$. For $\sigma>0$, the heat weight is differentiable in the variance, with
--   $$
--   \frac{\partial}{\partial\sigma}\,h\,\phi_\sigma(u-p)=\frac12\Bigl(\Bigl(\frac{u-p}\sigma\Bigr)^2-\frac1\sigma\Bigr)h\,\phi_\sigma(u-p) .
--   $$
--
--   This is the heat equation $\partial_\sigma\phi=\frac12\partial_p^2\phi$ written for a single weight.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/Gaussian.lean#L76-L91

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology

theorem OAI.TriangularHilbert.Heat.weight_hasDerivAt_variance (h u p σ : ℝ) (hσ : 0 < σ) :
    HasDerivAt (fun s => weight h u p s)
      ((1 / 2 : ℝ) * (score u p σ ^ 2 - σ⁻¹) * weight h u p σ) σ := by sorry
