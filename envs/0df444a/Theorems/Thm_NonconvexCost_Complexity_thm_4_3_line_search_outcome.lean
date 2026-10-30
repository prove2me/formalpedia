-- Prove2me | Theorems.Thm_NonconvexCost_Complexity_thm_4_3_line_search_outcome
-- name    : NonconvexCost.Complexity.thm_4_3_line_search_outcome
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:34.611987+00:00
-- url     : https://prove2.me/theorems/f09f9137-1072-4815-869d-bceaaf165df3
-- title:
--   Proof of Theorem 4.3, p. 9 — an insufficient-decrease trial gives average slope < −ε/6, and any t with h′₊(t) < 0 yields g′ ∈ ∂δf(x) with ⟨g′, g⟩ < |g|²/2
-- statement:
--   Let $\delta,\epsilon>0$, $f\colon X\to\mathbb R$, $G\colon X\times X\to X$, and let $x,g\in X$ with $|g|>\epsilon$. Put $\hat g=g/|g|$, $x(t)=x+(t-\delta)\hat g$, $x'=x(0)=x-\delta\hat g$, $h(t)=f(x(t))-\epsilon t/2$ and $h'_+(t)=\langle G(x(t),\hat g),\hat g\rangle-\epsilon/2$ on $[0,\delta]$. Suppose the trial step fails the sufficient-decrease test, $f(x)-f(x')<\delta\epsilon/3$. Then:
--
--   1. the average slope of $h$ on $[p,q]=[0,\delta]$ satisfies
--   $$\frac{h(q)-h(p)}{q-p}=\frac1\delta\Big(f(x)-\frac{\delta\epsilon}{2}-f(x')\Big)<-\frac{\epsilon}{6};$$
--   2. for every $t\in[0,\delta]$ with $h'_+(t)<0$, the vector $g'=G(x(t),\hat g)$ is a Goldstein subgradient, $g'\in\partial_\delta f(x)$, and $\langle g',g\rangle<\frac12|g|^2$.
--
--   This is the step of the proof of Theorem 4.3 that turns a successful line search into the input of Lemma 4.2.
--
--   **Formalization Note** That the bisection actually reaches such a $t$ is a separate statement (the per-line-search bound, proof of Theorem 6.6); here $t$ is any point of $[0,\delta]$ where the oracle formula for $h'_+$ is negative.
-- source:
--   Kong, Lewis, The cost of nonconvexity in deterministic nonsmooth optimization, arXiv:2210.00652v2, p. 9, proof of Theorem 4.3

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting
import Definitions.Def_NonconvexCost_Complexity_Algorithm

namespace NonconvexCost.Complexity

open Set
open scoped RealInnerProductSpace

theorem thm_4_3_line_search_outcome {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (x g : X)
    (hg : ε < ‖g‖) (hdec : f x - f (lsPoint δ x g 0) < δ * ε / 3) :
    (lsFun f δ ε x g δ - lsFun f δ ε x g 0) / (δ - 0) < -(ε / 6) ∧
      ∀ t ∈ Icc (0 : ℝ) δ, lsDeriv G δ ε x g t < 0 →
        G (lsPoint δ x g t) (‖g‖⁻¹ • g) ∈ goldstein G δ x ∧
          ⟪G (lsPoint δ x g t) (‖g‖⁻¹ • g), g⟫ < ‖g‖ ^ 2 / 2 := by sorry

end NonconvexCost.Complexity
