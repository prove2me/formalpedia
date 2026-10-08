-- Prove2me | Theorems.Thm_GivenDegreeSeq_FixedPoint_fixed_points_iff_ml_eq
-- name    : GivenDegreeSeq.FixedPoint.fixed_points_iff_ml_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:44.488663+00:00
-- url     : https://prove2.me/theorems/a2e97468-ce17-46f8-97f7-04face821e8c
-- title:
--   p. 9 — the fixed points of $\varphi$ are precisely the solutions of the ML equations (3)
-- statement:
--   Let $n\ge2$, let $d_1,\dots,d_n>0$, and let $\varphi:\mathbb R^n\to\mathbb R^n$ be the map $\varphi_i(x)=\log d_i-\log\sum_{j\ne i}r_{ij}(x)$ with $r_{ij}(x)=1/(e^{-x_j}+e^{x_i})$. Then for every $x\in\mathbb R^n$,
--   $$\varphi(x)=x\iff d_i=\sum_{j\ne i}\frac{e^{x_i+x_j}}{1+e^{x_i+x_j}}\quad\text{for all }i=1,\dots,n.$$
--
--   This identifies the maximum likelihood equations of the $\beta$-model with a fixed-point problem, which is what makes the iteration $x_{k+1}=\varphi(x_k)$ an algorithm for the MLE.
--
--   **Formalization Note** The hypotheses $n\ge2$ and $d_i>0$ are explicit: for $n=1$ the sum over $j\ne i$ is empty and $\log 0$ is a junk value in Lean, and $\log d_i$ needs $d_i>0$. Vertices are indexed by `Fin n`.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 9 (sentence before Theorem 1.5), with Eqs. (3)–(5)

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_Basic

namespace GivenDegreeSeq.FixedPoint

/-- p. 9: for `n ≥ 2` and positive degrees `d_1, …, d_n`, the fixed points of
`φ = (φ_1, …, φ_n)` are exactly the solutions of the ML equations (3). -/
theorem fixed_points_iff_ml_eq {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (x : Fin n → ℝ) :
    phi d x = x ↔ MLEq d x := by sorry

end GivenDegreeSeq.FixedPoint
