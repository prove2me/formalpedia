-- Prove2me | Theorems.Thm_NonconvexCost_Complexity_thm_6_6_line_search_calls
-- name    : NonconvexCost.Complexity.thm_6_6_line_search_calls
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:35.089976+00:00
-- url     : https://prove2.me/theorems/7ca49f05-121a-40dc-83cb-6b1b74b7d622
-- title:
--   Proof of Theorem 6.6, p. 18 — each line search of Algorithm 4.1 terminates within 1 + ⌊12Λ(δ)/ε⌋ oracle calls
-- statement:
--   Let $\delta,\epsilon>0$, let $C\subset X$ be convex, let $G$ be a directional subgradient map for $f$ on $C$, and suppose $f$ has finite nonconvexity modulus $\Lambda(\delta)$ on $C$. Let $x\in C$ and $g\in X$ with $|g|>\epsilon$, put $\hat g=g/|g|$, $x(t)=x+(t-\delta)\hat g$, $x'=x(0)$, $h(t)=f(x(t))-\epsilon t/2$ and $h'_+(t)=\langle G(x(t),\hat g),\hat g\rangle-\epsilon/2$, and suppose $x'\in C$ and $f(x)-f(x')<\delta\epsilon/3$. Then
--
--   1. $h'_+$ given by the oracle formula is the right derivative of $h$ at every point of $[0,\delta)$, and
--   2. the bisection method on $[0,\delta]$ (Corollary 5.6 with $\sigma=\epsilon/6$) terminates within
--   $$1+\Big\lfloor\frac{12\Lambda(\delta)}{\epsilon}\Big\rfloor$$
--   evaluations of $h'_+$, i.e. one of the first $1+\lfloor12\Lambda(\delta)/\epsilon\rfloor$ evaluations is negative.
--
--   Multiplying this by the number of line searches gives the complexity of Algorithm 4.1.
--
--   **Formalization Note** In the run of Algorithm 4.1 the hypothesis $x'\in C$ follows from the standing assumption on $x_0$ (iterates satisfy $f(x)\le f(x_0)$ and $|x'-x|=\delta$); it is stated here directly. Each evaluation is one oracle call, and that call also returns $G(x(t),\hat g)$, so no further call is needed to obtain the new subgradient.
-- source:
--   Kong, Lewis, The cost of nonconvexity in deterministic nonsmooth optimization, arXiv:2210.00652v2, p. 18, proof of Theorem 6.6

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting
import Definitions.Def_NonconvexCost_Complexity_Algorithm

namespace NonconvexCost.Complexity

theorem thm_6_6_line_search_calls {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (C : Set X) (hC : Convex ℝ C) (f : X → ℝ)
    (G : X → X → X) (hG : IsDirSubgradMapOn f G C)
    (hΛ : nonconvexityModulus f C δ ≠ ⊤) (x g : X) (hx : x ∈ C)
    (hx' : lsPoint δ x g 0 ∈ C) (hg : ε < ‖g‖)
    (hdec : f x - f (lsPoint δ x g 0) < δ * ε / 3) :
    IsRightDerivOn (lsFun f δ ε x g) (lsDeriv G δ ε x g) 0 δ ∧
      ¬ NoStopWithin (lsFun f δ ε x g) (lsDeriv G δ ε x g) 0 δ
        (1 + ⌊12 * (nonconvexityModulus f C δ).toReal / ε⌋₊) := by sorry

end NonconvexCost.Complexity
