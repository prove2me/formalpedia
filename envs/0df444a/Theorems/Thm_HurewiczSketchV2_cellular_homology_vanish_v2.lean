-- Prove2me | Theorems.Thm_HurewiczSketchV2_cellular_homology_vanish_v2
-- name    : HurewiczSketchV2.cellular_homology_vanish_v2
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T09:39:47.514553+00:00
-- url     : https://prove2.me/theorems/5fff487d-fde3-4034-9fce-c1fc71b7c1db
-- title:
--   Hurewicz step 2 (repaired) — homology vanishes for 0 < i < n+2
-- statement:
--   This is the **low-degree homology vanishing** step of the Hurewicz theorem.
--
--   Let $r=n+2\ge 2$ and let $Y$ be a reduced cellular model in degree $r$: its $(r-1)$-skeleton is a point, so the cellular chain complex of $Y$ starts in degree $r$. Hence the reduced homology of $Y$ vanishes below $r$:
--
--   $$
--   H_i(Y;\mathbb{Z})=0\qquad\text{for every }0<i<r .
--   $$
--
--   Degree $i=0$ is deliberately excluded: $H_0(Y;\mathbb Z)\cong\mathbb Z$ for any nonempty path-connected $Y$, so it is never zero here. The first possibly nonzero (reduced) homology group is $H_r(Y;\mathbb{Z})$, which the comparison step identifies with $\pi_r(Y,y)$.
--
--   **Formalization Note** `CategoryTheory.Limits.IsZero` is applied to the `ModuleCat ℤ` object `SP4Homology.H i Y`; the hypothesis `0 < i` rules out the degree where `TopCat.singularHomology₀Iso` identifies the group with a coproduct of copies of $\mathbb Z$ indexed by `ZerothHomotopy Y`.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.2 Theorem 4.32 p. 366: if X is (n-1)-connected with n >= 2 then H_i(X;Z)=0 for 0<i<n and h: pi_n(X) -> H_n(X) is an isomorphism; Tzuchien, 同伦论（5）：Hurewicz 定理, https://zhuanlan.zhihu.com/p/2063085365225863035, §2 定理 2.1.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Basic
import Definitions.Def_HurewiczSketchV2
import Definitions.Def_SP4Homology

set_option autoImplicit false

namespace HurewiczSketchV2

/-- Step 2 of the Hurewicz proof: a reduced CW model has no cells below degree `r = n + 2`, so
its cellular chain complex starts in degree `r` and all lower *reduced* singular homology
groups vanish.  Degree zero is excluded because H_0 of any nonempty space is Z, not zero. -/
theorem cellular_homology_vanish_v2 (n : ℕ) (Y : TopCat) (hY : ReducedCWModel (n + 2) Y) :
    ∀ i : ℕ, 0 < i → i < n + 2 → CategoryTheory.Limits.IsZero (SP4Homology.H i Y) := by
  sorry

end HurewiczSketchV2
