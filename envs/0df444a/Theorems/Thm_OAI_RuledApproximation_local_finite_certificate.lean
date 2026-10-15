-- Prove2me | Theorems.Thm_OAI_RuledApproximation_local_finite_certificate
-- name    : OAI.RuledApproximation.local_finite_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:46:55.547091+00:00
-- url     : https://prove2.me/theorems/0e9d0579-323b-4b44-9c15-b53e904f43d0
-- title:
--   A finite lattice certificate approximating all lines $p+r\,v(p)$ over a compact set
-- statement:
--   Equip $\mathbb{R}^2$ with the maximum norm $\|\cdot\|_\infty$ and with Lebesgue measure, and let $\Lambda_n=\tfrac1n\mathbb{Z}^2$. For a linear map $A:\mathbb{R}^2\to\mathbb{R}^2$ and real numbers $L,R$, say that $(A,L,R)$ is a *lattice model* if for every integer $n\ge1$, every $p\in\mathbb{R}^2$ and every $r$ with $|r|\le L$ there is $b\in\Lambda_n$ with
--   $$
--   \|b-p\|_\infty\le\frac Rn\qquad\text{and}\qquad\|(p-b)+rA(p-b)\|_\infty\le\frac1{2n}.
--   $$
--
--   Let $K\subseteq U\subseteq\mathbb{R}^2$ with $K$ compact and $U$ open, let $v:\mathbb{R}^2\to\mathbb{R}^2$ be any map, let $A$ be a linear map, and let $L,R,\delta$ be real numbers with $L\ge0$ and $\delta\ge0$ such that $(A,L,R)$ is a lattice model and
--   $$
--   \|v(p)-v(b)-A(p-b)\|_\infty\le\delta\,\|p-b\|_\infty\qquad\text{for all } p,b\in U.
--   $$
--   Let $F:\mathbb{R}^2\to\mathbb{R}$ be continuous with $F\ge0$, and let $\varepsilon>0$. Then there are an integer $n\ge1$ and a finite set $S\subseteq U$ such that
--
--   1. for every $p\in K$ and every $r$ with $|r|\le L$ there is $b\in S$ with
--   $$
--   \bigl\|\bigl(p+r\,v(p)\bigr)-\bigl(b+r\,v(b)\bigr)\bigr\|_\infty\le\frac{\tfrac12+L\delta R}{n};
--   $$
--   2. $\displaystyle\frac1{n^2}\sum_{b\in S}F(b)<\int_KF(p)\,dp+\varepsilon$.
--
--   Think of $p+r\,v(p)$ as the position at time $r$ of the line with label $p$ and direction field $v$. The result produces one finite set of labels $S$ that approximates every label of $K$ at every time $|r|\le L$ simultaneously, with an error of order $1/n$, while the weighted count of $S$ stays close to $\int_KF$. Turning each label $b\in S$ into a cylinder whose cross-section has width about $(1+2L\delta R)/n$ then gives the area estimate of the local covering.
--
--   **Formalization Note** The plane is `Parameter` (the type `Fin 2 → ℝ`, with its sup norm), the lattice model is `LatticeModel A L R`, $\Lambda_n$ is `coordinateGrid n`, and the sum is a `tsum` over the finite set $S$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/LocalApproximation.lean#L55-L89

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.local_finite_certificate {K U : Set Parameter} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (v : Parameter → Parameter)
    (A : Parameter →L[ℝ] Parameter) {L R delta : ℝ}
    (hL : 0 ≤ L) (hdelta : 0 ≤ delta) (hmodel : LatticeModel A L R)
    (hrem : ∀ p ∈ U, ∀ b ∈ U,
      ‖v p - v b - A (p - b)‖ ≤ delta * ‖p - b‖)
    {F : Parameter → ℝ} (hF : Continuous F) (hFpos : ∀ p, 0 ≤ F p)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ n : ℕ, 0 < n ∧ ∃ S : Set Parameter, S.Finite ∧ S ⊆ U ∧
      (∀ p ∈ K, ∀ r : ℝ, |r| ≤ L → ∃ b ∈ S,
        ‖p + r • v p - (b + r • v b)‖ ≤ (1 / 2 + L * delta * R) / n) ∧
      (∑' b : S, F b) / (n : ℝ) ^ 2 < (∫ p in K, F p) + eps := by sorry
