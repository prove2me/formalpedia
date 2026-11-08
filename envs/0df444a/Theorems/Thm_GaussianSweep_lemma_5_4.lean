-- Prove2me | Theorems.Thm_GaussianSweep_lemma_5_4
-- name    : GaussianSweep.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:13.91511+00:00
-- url     : https://prove2.me/theorems/6f86cd38-7d1b-46b3-ac8c-56a05d371559
-- title:
--   Lemma 5.4 — edge correlations of padded labels: $\mathrm{Corr}(Y_u,Y_v) \ge r_{pp}(1-\frac1R)$
-- statement:
--   Let $p \ge 3$ and $R \ge 1$ be integers, let $G$ be a finite graph with maximum degree $\Delta(G) \le p$, and let $(Y_v)$ be the padded labels of degree $p$ at radius $R$, built from independent standard normal variables $(Z_w)_{w \in V(G)}$. Then every edge $uv$ satisfies
--   $$
--   \mathrm{Corr}(Y_u, Y_v) \ge r_{pp}\Big(1 - \frac1R\Big), \qquad r_{pp} = \frac{2\sqrt{p-1}}{p}.
--   $$
--   For $p = 3$ this gives the correlation level $r^*(1 - 1/R)$, $r^* = 2\sqrt2/3$, of the geometric labels, which is the input of every star bound in the proof of Theorem 8.1.
--
--   **Formalization Note** $\mathrm{Corr}$ is the covariance divided by the square root of the product of the variances, all under the product Gaussian measure.
--
--   Differences from the source:
--   - encoding: independent N(0, 1) variables (Z_w)_{w ∈ V(G)} → the coordinates of a point z : V → ℝ under the product measure Measure.pi (fun _ => gaussianReal 0 1); reason: canonical probability space of the family; same random vector
--   - encoding: a finite simple graph G → a SimpleGraph on a finite vertex type V (Fintype), n = card V; reason: every finite graph is isomorphic to one on a finite type; pathwidth and degrees are invariant
--   - encoding: Corr(Y_u, Y_v) → cov[Y_u, Y_v] / √(Var[Y_u] · Var[Y_v]) under the product measure; reason: the definition of the correlation; the variances are 1 by Lemma 5.6(i)
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 5.4, p.29 (PDF p.31); r_pp from (5.3), p.29

import Mathlib
import Definitions.Def_GaussianSweep_paddedLabel
open MeasureTheory ProbabilityTheory

namespace GaussianSweep

/-- Lemma 5.4 (edge correlations, padded labels) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 5.4, p.29 (PDF p.31)). Let
`p ≥ 3` and `R ≥ 1` be integers, `G` a graph with `Δ(G) ≤ p`, and `(Y_v)` the padded labels of
degree `p`. Then every edge `uv` satisfies `Corr(Y_u, Y_v) ≥ r_pp (1 − 1/R)`, where
`r_pp = 2√(p − 1)/p` (5.3).

**Formalization Note** The independent `N(0, 1)` variables are the coordinates of `z : V → ℝ`
under `Measure.pi fun _ => gaussianReal 0 1`; `Corr = Cov/√(Var·Var)` under that measure. -/
theorem lemma_5_4 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (p R : ℕ)
    (hp : 3 ≤ p) (hR : 1 ≤ R) (hΔ : G.maxDegree ≤ p) (u v : V) (huv : G.Adj u v) :
    2 * Real.sqrt ((p : ℝ) - 1) / p * (1 - 1 / (R : ℝ)) ≤
      cov[paddedLabel G p R u, paddedLabel G p R v; Measure.pi fun _ : V => gaussianReal 0 1] /
        Real.sqrt (Var[paddedLabel G p R u; Measure.pi fun _ : V => gaussianReal 0 1] *
          Var[paddedLabel G p R v; Measure.pi fun _ : V => gaussianReal 0 1]) := by sorry

end GaussianSweep
