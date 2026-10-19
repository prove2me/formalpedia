-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_mesh_mass_le
-- name    : OAI.TriangularHilbert.Heat.mesh_mass_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:34:55.612699+00:00
-- url     : https://prove2.me/theorems/eaede7b7-4a4a-4e6f-a7ff-ee029540508c
-- title:
--   Gaussian Riemann sums on a grid are uniformly bounded
-- statement:
--   The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$. Let $h>0$ and $\sigma\ge h^2$. Then for every offset $c\in\mathbb R$ and every $n$,
--   $$
--   \sum_{i=0}^{n-1}h\,\phi_\sigma(c+hi)\le2e^{1/2} .
--   $$
--
--   A grid whose mesh is at most the standard deviation sees total heat weight bounded independently of the number of points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MeshMass.lean#L63-L97

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology BigOperators

theorem OAI.TriangularHilbert.Heat.mesh_mass_le {h σ : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (c : ℝ) (n : ℕ) :
    (∑ i : Fin n, h*density σ (c+h*i)) ≤ meshMassConstant := by sorry
