-- Prove2me | Theorems.Thm_HurewiczSketchV2_cellular_hurewicz_isomorphism
-- name    : HurewiczSketchV2.cellular_hurewicz_isomorphism
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T07:07:59.739037+00:00
-- url     : https://prove2.me/theorems/60eb9b9a-1fc9-5234-8603-696430d03e59
-- title:
--   Hurewicz step 3 (repaired) — cellular comparison on the CW model
-- statement:
--   This is the **cellular comparison** step of the Hurewicz theorem. Let $r=n+2\ge 2$ and let $(Y,y)$ be a reduced cellular model in degree $r$, so that $H_i(Y;\mathbb{Z})=0$ for all $i<r$. Then the Hurewicz homomorphism is an isomorphism of abelian groups:
--
--   $$
--   h_r:\pi_r(Y,y)\;\xrightarrow{\;\cong\;}\;H_r(Y;\mathbb{Z}).
--   $$
--
--   Each $r$-cell of $Y$ gives a generator of both $\pi_r(Y^r)$ and the cellular chain group $C_r(Y)$, and the attaching maps of the $(r+1)$-cells give the same relations on the two sides, namely the image of $d_{r+1}$. The middle Hurewicz map sends a cellular generator to the identically named cellular chain, so it is an isomorphism and the two cokernels agree.
--
--   **Formalization Note** The conclusion is an `AddEquiv` between `Additive (HomotopyGroup.Pi (n+2) Y y)` and `SP4Homology.H (n+2) Y`. The lower-degree vanishing hypothesis is kept explicit to record its role in the cellular argument.
-- source:
--   Tzuchien, 同伦论（5）：Hurewicz 定理, https://zhuanlan.zhihu.com/p/2063085365225863035, §2 定理 2.1 证明第一步至第三步; A. Hatcher, Algebraic Topology, Cambridge University Press (2002), Theorem 4.32, p. 366.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Basic
import Definitions.Def_HurewiczSketchV2
import Definitions.Def_SP4Homology

set_option autoImplicit false

namespace HurewiczSketchV2

/-- Step 3 of the Hurewicz proof: cellular comparison.  On a reduced CW model, `r`-cells give
generators of both `π_r` and the cellular chain group, while `(r+1)`-cells give the same
relations; the Hurewicz homomorphism is therefore an isomorphism. -/
theorem cellular_hurewicz_isomorphism (n : ℕ) (Y : TopCat) (y : Y)
    (hY : ReducedCWModel (n + 2) Y)
    (hH : ∀ i : ℕ, i < n + 2 → CategoryTheory.Limits.IsZero (SP4Homology.H i Y)) :
    Nonempty (Additive (HomotopyGroup.Pi (n + 2) Y y) ≃+ SP4Homology.H (n + 2) Y) := by
  sorry

end HurewiczSketchV2
