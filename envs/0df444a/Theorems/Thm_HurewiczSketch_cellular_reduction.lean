-- Prove2me | Theorems.Thm_HurewiczSketch_cellular_reduction
-- name    : HurewiczSketch.cellular_reduction
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-25T13:09:59.996296+00:00
-- url     : https://prove2.me/theorems/6b93a37b-9ff4-4653-be14-29058f05b48e
-- title:
--   Hurewicz step 1 — cellular reduction to a model with collapsed low skeleton
-- statement:
--   This is the **cellular reduction** step of the Hurewicz theorem. Let $X$ be a topological space with base point $x$, and suppose $X$ is $(n+1)$-connected, i.e. $\pi_k(X,x)=0$ for every $k\le n+1$. Put $r=n+2\ge 2$. Then there exists a pointed CW model $(Y,y)$ whose $(r-1)$-skeleton is a point, together with additive isomorphisms
--
--   $$
--   \pi_r(Y,y)\;\cong\;\pi_r(X,x),\qquad H_r(Y;\mathbb{Z})\;\cong\;H_r(X;\mathbb{Z}).
--   $$
--
--   The model is reduced in the sense that all its homotopy groups in degrees below $r$ vanish. These two isomorphisms are what lets the computation be carried out on $Y$ and then transferred back to $X$.
--
--   **Formalization Note** The transfer is packaged as the existence of `AddEquiv`s between the additively written homotopy groups and between the underlying abelian groups of the singular homology objects; Mathlib has no functorial map on `HomotopyGroup.Pi`, so the weak-equivalence-induced isomorphisms are recorded this way. `Y` is a `TopCat` object so that its topology is bundled.
-- source:
--   Tzuchien, 同伦论（5）：Hurewicz 定理, https://zhuanlan.zhihu.com/p/2063085365225863035, §2 定理 2.1 证明第一步至第三步; A. Hatcher, Algebraic Topology, Cambridge University Press (2002), Theorem 4.32, p. 366.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Basic
import Definitions.Def_HurewiczSketch
import Definitions.Def_SP4Homology

set_option autoImplicit false

namespace HurewiczSketch

/-- Step 1 of the Hurewicz proof: cellular reduction.  An `(n+1)`-connected space is weakly
equivalent to a reduced CW model whose `(n+1)`-skeleton is a point; in particular the model has
trivial lower homotopy groups, and its `(n+2)`nd homotopy and homology groups agree with those
of the original space. -/
theorem cellular_reduction (n : ℕ) (X : Type) [TopologicalSpace X] (x : X)
    (hconn : ∀ k : ℕ, k ≤ n + 1 → Subsingleton (HomotopyGroup.Pi k X x)) :
    ∃ (Y : TopCat) (y : Y),
      ReducedCWModel (n + 2) Y ∧
        Nonempty (Additive (HomotopyGroup.Pi (n + 2) Y y) ≃+ Additive (HomotopyGroup.Pi (n + 2) X x)) ∧
        Nonempty (SP4Homology.H (n + 2) Y ≃+ SP4Homology.H (n + 2) X) := by
  sorry

end HurewiczSketch
