-- Prove2me | Theorems.Thm_OAI_FourRow_pair_stability_one
-- name    : OAI.FourRow.pair_stability_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T17:50:38.017982+00:00
-- url     : https://prove2.me/theorems/c9255bb3-d9f7-424d-a00a-2b214e1dc711
-- title:
--   The squared pair-permanent deficit controls the distance of a normalized nonnegative row from the all-ones vector
-- statement:
--   Let $a=(a_0,a_1,a_2,a_3)$ and $b=(b_0,b_1,b_2,b_3)$ be vectors in $\mathbb{R}^4$ with nonnegative entries, normalized so that $\sum_{j=0}^{3}a_j^2=4$ and $\sum_{j=0}^{3}b_j^2=4$ (mean square $1$, as for the all-ones vector $\mathbf{1}=(1,1,1,1)$). For a pair of indices $k<l$, the number $a_kb_l+a_lb_k$ is the permanent of the $2\times2$ submatrix in columns $k,l$ of the $2\times4$ matrix with rows $a$ and $b$. Let
--   $$
--   Q(a,b)=\sum_{0\le k<l\le3}\bigl(a_kb_l+a_lb_k\bigr)^2
--   $$
--   be the sum of the squares of these six pair permanents. Then
--   $$
--   \sum_{j=0}^{3}(a_j-1)^2\le9\,\bigl(24-Q(a,b)\bigr).
--   $$
--
--   For $a=b=\mathbf{1}$ every pair permanent equals $2$, so $Q(\mathbf{1},\mathbf{1})=24$ and both sides vanish. Since the left-hand side is nonnegative, the inequality implies $Q(a,b)\le24$ for all normalized nonnegative pairs, and it is a quantitative stability statement: a small deficit $24-Q(a,b)$ forces $a$ to be close to $\mathbf{1}$ in squared Euclidean distance (and, as $Q(a,b)=Q(b,a)$, the same holds for $b$). It is the basic exponent-two stability estimate of the robust four-row permanent inequality, where it is applied to the row pairs $(f_0,f_1)$ and $(f_2,f_3)$ of a $4\times4$ array $f$.
--
--   **Formalization Note** Rows are real functions on `Fin 4`. The hypotheses are `rowSq a = 4` and `rowSq b = 4` together with entrywise nonnegativity, the left-hand side is `rowDist a`, and $Q(a,b)$ is `pairSq a b`, the sum of squares of the six-entry vector `pairEntries a b`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Permanent/Stability.lean#L56-L108

import Mathlib
import Definitions.Def_FourRowPermanent
import Definitions.Def_OAI_Combinatorics_Permanent_Stability

open OAI OAI.FourRow
open scoped BigOperators

theorem OAI.FourRow.pair_stability_one (a b : Site → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (haq : rowSq a = 4) (hbq : rowSq b = 4) :
    rowDist a ≤ 9 * (24 - pairSq a b) := by sorry
