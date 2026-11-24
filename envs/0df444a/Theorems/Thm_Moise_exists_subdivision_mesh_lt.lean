-- Prove2me | Theorems.Thm_Moise_exists_subdivision_mesh_lt
-- name    : Moise.exists_subdivision_mesh_lt
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T20:41:39.350933+00:00
-- url     : https://prove2.me/theorems/280b4604-c0a2-43dd-85e2-721fe750873e
-- title:
--   Existence of subdivisions with arbitrarily small mesh
-- statement:
--   Let $K$ be a finite Euclidean complex in $\mathbb{R}^n$ and let $\varepsilon > 0$. Then there exists a finite subdivision $K'$ of $K$ such that every simplex $\sigma \in K'$ has diameter $\operatorname{diam}(|\sigma|) < \varepsilon$.
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapter 0.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_Moise_EuclideanComplex

namespace Moise

theorem exists_subdivision_mesh_lt {n : ℕ} (K : EuclideanComplex n) (hfin : K.IsFinite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : EuclideanComplex n, K'.IsFinite ∧ K'.IsSubdivision K ∧
      ∀ σ ∈ K'.simplices, Metric.diam σ.carrier < ε := by sorry

end Moise
