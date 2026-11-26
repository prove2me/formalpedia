-- Prove2me | Theorems.Thm_HurewiczSketchV2_cellular_hurewicz_isomorphism_v2
-- name    : HurewiczSketchV2.cellular_hurewicz_isomorphism_v2
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T09:39:45.814926+00:00
-- url     : https://prove2.me/theorems/09ff4e46-846d-5c1b-ae2f-ac2d3627c311
-- title:
--   Hurewicz step 3 (repaired) — cellular comparison with corrected range
-- statement:
--   This is the **cellular comparison** step of the Hurewicz theorem.
--
--   Let $r=n+2\ge 2$, let $Y$ be a reduced cellular model in degree $r$ with base point $y$, and assume $H_i(Y;\mathbb{Z})=0$ for every $0<i<r$. On such a model the $r$-cells give generators of both $\pi_r(Y,y)$ and the cellular chain group $C_r$, while the $(r+1)$-cells give the same relations; hence the Hurewicz map is an isomorphism
--
--   $$
--   h_r:\pi_r(Y,y)\;\xrightarrow{\sim}\;H_r(Y;\mathbb{Z}).
--   $$
--
--   **Formalization Note** The conclusion is an `AddEquiv` between the additively written homotopy group `Additive (HomotopyGroup.Pi (n+2) Y y)` and the underlying abelian group of `SP4Homology.H (n+2) Y`. The hypothesis uses the corrected range `0 < i < n+2`, matching the repaired homology-vanishing child.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.2 Theorem 4.32 p. 366: if X is (n-1)-connected with n >= 2 then H_i(X;Z)=0 for 0<i<n and h: pi_n(X) -> H_n(X) is an isomorphism; Tzuchien, 同伦论（5）：Hurewicz 定理, https://zhuanlan.zhihu.com/p/2063085365225863035, §2 定理 2.1.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Basic
import Definitions.Def_HurewiczSketchV2
import Definitions.Def_SP4Homology

set_option autoImplicit false

namespace HurewiczSketchV2

/-- Step 3 of the Hurewicz proof: cellular comparison.  On a reduced CW model, `r`-cells give
generators of both `π_r` and the cellular chain group, while `(r+1)`-cells give the same
relations; the Hurewicz homomorphism is therefore an isomorphism. -/
theorem cellular_hurewicz_isomorphism_v2 (n : ℕ) (Y : TopCat) (y : Y)
    (hY : ReducedCWModel (n + 2) Y)
    (hH : ∀ i : ℕ, 0 < i → i < n + 2 → CategoryTheory.Limits.IsZero (SP4Homology.H i Y)) :
    Nonempty (Additive (HomotopyGroup.Pi (n + 2) Y y) ≃+ SP4Homology.H (n + 2) Y) := by
  sorry

end HurewiczSketchV2
