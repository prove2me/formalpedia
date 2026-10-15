-- Prove2me | Theorems.Thm_OAI_FourRow_normalized_uniform_stability
-- name    : OAI.FourRow.normalized_uniform_stability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T17:51:49.140679+00:00
-- url     : https://prove2.me/theorems/2ceb8400-2da0-429b-90bd-4e239e40fdcb
-- title:
--   Quantitative stability of the bound $\operatorname{per}(f)\le24$ for nonnegative $4\times4$ arrays with normalized rows
-- statement:
--   Let $f=(f_{ij})_{i,j=0}^{3}$ be a real $4\times4$ array with nonnegative entries whose rows are normalized by $\sum_{j=0}^{3}f_{ij}^2=4$ for each $i$. Let $u$ be the uniform law on the symmetric group $S_4$, $u(\pi)=\tfrac1{24}$, and let $\Delta(f)=\sum_{i,j=0}^{3}(f_{ij}-1)^2$ be the squared Frobenius distance from $f$ to the all-ones matrix $J$. Then
--   $$
--   \sum_{\pi\in S_4}\frac{1}{24}\prod_{i=0}^{3}f_{i\pi(i)}\le1-\frac{\Delta(f)}{1728}.
--   $$
--   The left-hand side is the expectation of $\prod_if_{i\pi(i)}$ for a uniformly random permutation $\pi$, that is, $\operatorname{per}(f)/24$.
--
--   With the normalized $\ell^2$ row norms $\|f_i\|_2=\bigl(\tfrac14\sum_jf_{ij}^2\bigr)^{1/2}=1$, the weaker consequence $\operatorname{per}(f)/24\le1=\prod_i\|f_i\|_2$ is the exponent-two case of the four-row permanent inequality for the uniform law, with equality at $f=J$. The theorem is a quantitative stability version of it: the deficit is at least proportional to the squared distance of $f$ from $J$. This gain is what allows the exponent to be lowered slightly below $2$ and the uniform law to be replaced by nearby laws with uniform marginals.
--
--   **Formalization Note** The left-hand side is `permanentExpectation uniformLaw f`, the normalization is `rowSq (f i) = 4` for every row index, and $\Delta(f)$ is `totalDist f`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Permanent/Stability.lean#L169-L199

import Mathlib
import Definitions.Def_FourRowPermanent
import Definitions.Def_OAI_Combinatorics_Permanent_Stability

open OAI OAI.FourRow
open scoped BigOperators

theorem OAI.FourRow.normalized_uniform_stability (f : Functions)
    (hf : ∀ i j, 0 ≤ f i j) (hn : ∀ i, rowSq (f i) = 4) :
    permanentExpectation uniformLaw f ≤ 1 - totalDist f / 1728 := by sorry
