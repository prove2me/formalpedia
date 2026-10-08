-- Prove2me | Theorems.Thm_GivenDegreeSeq_MLE_x0_sub_x1_at_beta
-- name    : GivenDegreeSeq.MLE.x0_sub_x1_at_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:10.735894+00:00
-- url     : https://prove2.me/theorems/7dd495bd-340c-40c1-89f3-2693b2685b40
-- title:
--   Proof of Theorem 1.3, p. 21 — with $x_0=\beta$, $(x_0-x_1)_i=\log(\bar d_i/d_i)$
-- statement:
--   Let $n\ge 2$, let $d_1,\dots,d_n>0$, let $\beta\in\mathbb R^n$, and let $\bar d_i=\sum_{j\ne i}e^{\beta_i+\beta_j}/(1+e^{\beta_i+\beta_j})$ be the expected degree of vertex $i$ under $\mathbb P_\beta$. With $x_0=\beta$ and $x_1=\varphi(x_0)$, where $\varphi$ is the map of (4)–(5) built from $d$, for every $i$
--   $$(x_0-x_1)_i=\log\frac{\bar d_i}{d_i}.$$
--
--   This identity converts the a-priori bound $|x_0-\hat\beta|_\infty\le C|x_0-x_1|_\infty$ of Theorem 1.5 into a bound on $|\hat\beta-\beta|_\infty$ by the relative deviation of the observed degrees from their means.
--
--   **Formalization Note** The identity is stated for every positive vector $d$, not only observed degree sequences; $n\ge 2$ makes the sum over $j\ne i$ nonempty, so $\bar d_i>0$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 21, proof of Theorem 1.3

import Mathlib
import Definitions.Def_GivenDegreeSeq_MLE_Basic

namespace GivenDegreeSeq.MLE

/-- Proof of Theorem 1.3, p. 21. Let `n ≥ 2` and let `d` be a vector of positive degrees. With
`x₀ = β` and `x₁ = φ(x₀)`, the `i`-th component of `x₀ − x₁` is `log(d̄_i / d_i)`, where
`d̄_i = Σ_{j ≠ i} e^{β_i+β_j}/(1 + e^{β_i+β_j})`. -/
theorem x0_sub_x1_at_beta (n : ℕ) (hn : 2 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (β : Fin n → ℝ) (i : Fin n) :
    (β - GivenDegreeSeq.FixedPoint.phi d β) i = Real.log (dbar β i / d i) := by sorry

end GivenDegreeSeq.MLE
