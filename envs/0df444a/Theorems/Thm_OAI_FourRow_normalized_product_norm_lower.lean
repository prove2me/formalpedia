-- Prove2me | Theorems.Thm_OAI_FourRow_normalized_product_norm_lower
-- name    : OAI.FourRow.normalized_product_norm_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T17:52:21.406981+00:00
-- url     : https://prove2.me/theorems/fc19d6d4-7e28-4830-aee6-1740cf2263e2
-- title:
--   Lower bound for the product of normalized $\ell^p$ row norms of a $4\times4$ array for $9/5\le p\le2$
-- statement:
--   Let $p$ be a real number with $9/5\le p\le2$. For a row $g=(g_0,g_1,g_2,g_3)$ with nonnegative entries let
--   $$
--   \|g\|_p=\Bigl(\frac14\sum_{j=0}^{3}g_j^{\,p}\Bigr)^{1/p}
--   $$
--   be its $\ell^p$ norm with respect to the uniform probability on the four sites. Let $f=(f_{ij})_{i,j=0}^{3}$ be a real $4\times4$ array with nonnegative entries whose rows $f_i$ are normalized by $\sum_{j=0}^{3}f_{ij}^2=4$, and let $\Delta(f)=\sum_{i,j=0}^{3}(f_{ij}-1)^2$ be its squared Frobenius distance from the all-ones matrix. Then
--   $$
--   1-\frac{5(2-p)}{8}\,\Delta(f)\le\prod_{i=0}^{3}\|f_i\|_p .
--   $$
--
--   The normalization says $\|f_i\|_2=1$ for every row, so the theorem bounds how much the product of row norms can drop when the exponent is lowered from $2$ to $p$: the loss is at most linear in $2-p$ and in the squared distance $\Delta(f)$ of $f$ from the all-ones matrix. In the robust four-row permanent inequality this loss is absorbed by the gain $\Delta(f)/1728$ of the exponent-two stability estimate once $p$ is close enough to $2$.
--
--   **Formalization Note** The norm is `lpNorm p g`, defined with real powers (`Real.rpow`) as the $(1/p)$-th power of the average of the $p$-th powers; for nonnegative entries and $p>0$ these are the usual powers. The normalization is `rowSq (f i) = 4` and $\Delta(f)$ is `totalDist f`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Permanent/Norm.lean#L112-L133

import Mathlib
import Definitions.Def_FourRowPermanent
import Definitions.Def_OAI_Combinatorics_Permanent_Stability

open OAI OAI.FourRow
open scoped BigOperators

theorem OAI.FourRow.normalized_product_norm_lower (p : ℝ) (hp0 : 9 / 5 ≤ p) (hp2 : p ≤ 2)
    (f : Functions) (hf : ∀ i j, 0 ≤ f i j) (hn : ∀ i, rowSq (f i) = 4) :
    1 - (5 * (2 - p) / 8) * totalDist f ≤ ∏ i, lpNorm p (f i) := by sorry
