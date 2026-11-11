-- Prove2me | Theorems.Thm_OptimalLCA_Matching_lemma_4_4
-- name    : OptimalLCA.Matching.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:47:00.394167+00:00
-- url     : https://prove2.me/theorems/36c51bd9-d1de-4cf4-a962-898fc9e93a89
-- title:
--   Lemma 4.4 — Algorithm 1 returns the unique minimizer of (4.8); optimality condition (4.9)
-- statement:
--   Fix an interior base $z=(x,q)$, a vector $v=(v_x,v_q)$, candidate distributions $h\in Q$ and $\alpha\ge10$. Then $y=\mathrm{Resp}_{z,v}(h)$ (Algorithm 1) is the unique minimizer over $y\in X$ of
--   $$\langle v_x,y\rangle+D^\alpha_z(y,h),\tag{4.8}$$
--   it lies in $(-1,1)^V$, and with $\tau=\operatorname{atanh}x$, $\tau'=\operatorname{atanh}y$,
--   $$(1+\ell(h))\tau'=(1+\ell(q))\tau-\tfrac12v_x,\tag{4.9}$$
--   equivalently $\tau'=A\tau+B$ with $A=\frac{1+\ell(q)}{1+\ell(h)}$, $B=-\frac{v_x}{2(1+\ell(h))}$ (and $y=\tanh\tau'$).
--
--   Differences from the source:
--   - encoding: atanh → Real.artanh (log √((1+x)/(1−x))); reason: equals ½ log((1+x)/(1−x)) on (−1, 1)
--   - encoding: unique minimizer → y ∈ X and every other y′ ∈ X has strictly larger objective; reason: definition of a unique minimizer
--   - encoding: a graph with vertex set [n] → any finite vertex type V with a SimpleGraph (decidable adjacency); reason: relabelling; every graph on [n] is an instance
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 20, Lemma 4.4, (4.8), (4.9), Algorithm 1

import Mathlib
import Definitions.Def_OptimalLCA_Matching_SaddlePoint

namespace OptimalLCA.Matching

/-- Lemma 4.4 (box response). For an interior base `z = (x, q)`, a vector `v = (v_x, v_q)`,
candidate distributions `h ∈ Q` and `α ≥ 10`, `y = Resp_{z,v}(h)` is the unique minimizer
over `X` of `⟨v_x, y⟩ + D^α_z(y, h)` (4.8); it lies in `(-1, 1)^V`; with `τ = atanh x`,
`τ' = atanh y`, `(1 + ℓ(h)) τ' = (1 + ℓ(q)) τ - ½ v_x` (4.9); equivalently `τ' = Aτ + B`
with `A = (1 + ℓ(q))/(1 + ℓ(h))`, `B = -v_x/(2(1 + ℓ(h)))`. -/
theorem lemma_4_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (α : ℝ) (hα : 10 ≤ α) (z v : StateSpace G) (h : Idx G → ℝ)
    (hz : IsInteriorBase G z) (hh : InQ G h) :
    (InX (resp G z v h) ∧
      ∀ y : V → ℝ, InX y → y ≠ resp G z v h →
        ∑ j, v.1 j * resp G z v h j + bregman G Finset.univ α z (resp G z v h, h) <
          ∑ j, v.1 j * y j + bregman G Finset.univ α z (y, h)) ∧
    (∀ j, resp G z v h j ∈ Set.Ioo (-1 : ℝ) 1) ∧
    (∀ j, (1 + load G h j) * Real.artanh (resp G z v h j) =
        (1 + load G z.2 j) * Real.artanh (z.1 j) - (1 / 2) * v.1 j) ∧
    (∀ j, Real.artanh (resp G z v h j) =
        (1 + load G z.2 j) / (1 + load G h j) * Real.artanh (z.1 j) +
          -(v.1 j) / (2 * (1 + load G h j))) := by sorry

end OptimalLCA.Matching
