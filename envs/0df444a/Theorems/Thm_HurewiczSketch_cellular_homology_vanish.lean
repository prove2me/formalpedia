-- Prove2me | Theorems.Thm_HurewiczSketch_cellular_homology_vanish
-- name    : HurewiczSketch.cellular_homology_vanish
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-25T13:09:51.933327+00:00
-- url     : https://prove2.me/theorems/33426359-78b0-5bd5-ba95-a2e7cd073c5e
-- title:
--   Hurewicz step 2 — vanishing of homology below the first degree
-- statement:
--   This is the **low-degree homology computation** in the Hurewicz theorem. Let $r\ge 2$ and let $Y$ be a reduced cellular model in degree $r$: its $(r-1)$-skeleton is a point. Then the cellular chain groups of $Y$ vanish in every degree below $r$, hence
--
--   $$
--   H_i(Y;\mathbb{Z})=0\qquad\text{for every }i<r.
--   $$
--
--   Only the vanishing clause is recorded here; the first possibly nonzero homology group is $H_r(Y;\mathbb{Z})$, which is the homology group compared with $\pi_r(Y,y)$ in the cellular comparison step.
--
--   **Formalization Note** `IsZero` is the category-theoretic zero-object predicate applied to the `ModuleCat ℤ` object `SP4Homology.H i Y`; it expresses that the abelian homology group is trivial.
-- source:
--   Tzuchien, 同伦论（5）：Hurewicz 定理, https://zhuanlan.zhihu.com/p/2063085365225863035, §2 定理 2.1 证明第一步至第三步; A. Hatcher, Algebraic Topology, Cambridge University Press (2002), Theorem 4.32, p. 366.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Basic
import Definitions.Def_HurewiczSketch
import Definitions.Def_SP4Homology

set_option autoImplicit false

namespace HurewiczSketch

/-- Step 2 of the Hurewicz proof: a reduced CW model has no cells below degree `r = n + 2`, so
its cellular chain complex starts in degree `r` and all lower singular homology groups vanish. -/
theorem cellular_homology_vanish (n : ℕ) (Y : TopCat) (hY : ReducedCWModel (n + 2) Y) :
    ∀ i : ℕ, i < n + 2 → CategoryTheory.Limits.IsZero (SP4Homology.H i Y) := by
  sorry

end HurewiczSketch
