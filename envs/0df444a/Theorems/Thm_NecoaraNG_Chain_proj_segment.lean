-- Prove2me | Theorems.Thm_NecoaraNG_Chain_proj_segment
-- name    : NecoaraNG.Chain.proj_segment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:47:01.004994+00:00
-- url     : https://prove2.me/theorems/8b06b54e-bb52-4d1f-ac3f-f4bcc3ffdd80
-- title:
--   Proof of Theorem 3, p. 8 — the projection onto X* is constant along the segment from x̄ to x
-- statement:
--   Let $X\subseteq\mathbb R^n$ be convex, let $f$ be convex on $X$, and let $X^*=\arg\min_{x\in X}f(x)$ contain a point $x^*$. Let $x\in X$ and let $\bar x=[x]_{X^*}$ be a nearest point of $X^*$ to $x$. Then for every $t\in[0,1]$, $\bar x$ is also a nearest point of $X^*$ to $\bar x+t(x-\bar x)$:
--   $$[\bar x+t(x-\bar x)]_{X^*}=\bar x\qquad\text{for all } t\in[0,1].$$
--
--   This is the fact used in the proofs of Theorems 1 and 3: along the segment $[\bar x,x]$ the projection onto the optimal set does not move, so (10) or (17) can be applied at every point of the segment with the same $\bar x$.
--
--   **Formalization Note** The conclusion is stated with the nearest-point predicate: $\bar x\in X^*$ and $\|\bar x+t(x-\bar x)-\bar x\|\le\|\bar x+t(x-\bar x)-z\|$ for all $z\in X^*$. The hypotheses on $X$ and $f$ are the paper's standing ones (they make $X^*$ convex); the closedness of $X$ and the Lipschitz gradient are not needed and are omitted.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 8, proof of Theorem 3, sentence after the display

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting

namespace NecoaraNG.Chain

open scoped InnerProductSpace

/-- Projection invariance along the segment `[x̄, x]` (proof of Theorem 3, p. 8):
if `x̄ = [x]_{X*}` then `[x̄ + t (x - x̄)]_{X*} = x̄` for every `t ∈ [0, 1]`. -/
theorem proj_segment {n : ℕ} (X : Set (E n)) (hXconv : Convex ℝ X)
    (f : E n → ℝ) (hf : ConvexOn ℝ X f) (xstar : E n) (hxstar : xstar ∈ optSet X f) :
    ∀ x ∈ X, ∀ xbar, IsNearest (optSet X f) x xbar →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, IsNearest (optSet X f) (xbar + t • (x - xbar)) xbar := by sorry

end NecoaraNG.Chain
