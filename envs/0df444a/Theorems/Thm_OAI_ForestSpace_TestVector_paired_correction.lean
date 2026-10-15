-- Prove2me | Theorems.Thm_OAI_ForestSpace_TestVector_paired_correction
-- name    : OAI.ForestSpace.TestVector.paired_correction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:17:00.565448+00:00
-- url     : https://prove2.me/theorems/f3dabf9e-3a29-42c8-ba62-84cb5b23a36b
-- title:
--   Paired corrections in the disjoint-segment norm: $\|f+s(c\pm k)\|\le\sqrt{1+12s^2}$
-- statement:
--   Let $V$ be a partially ordered set that is a *forest* (whenever $a\le c$ and $b\le c$, the elements $a,b$ are comparable) and has *finite ancestor sets* ($\{w:\ w\le v\}$ is finite for every $v$). On the space $c_{00}(V)$ of finitely supported functions $u:V\to\mathbb{R}$ consider the disjoint-segment norm
--   $$
--   \|u\|=\Bigl(\sup\Bigl\{\sum_{i\in I}\Bigl(\sum_{v\in S_i}u(v)\Bigr)^2\Bigr\}\Bigr)^{1/2},
--   $$
--   the supremum over all finite families $(S_i)_{i\in I}$ of pairwise disjoint segments (finite order-convex chains).
--
--   **Theorem.** Let $H\subseteq V$ be a lower set and $f,k\in c_{00}(V)$ with $f$ vanishing outside $H$, $k$ vanishing on $H$, $\|f\|\le1$ and $\|k\|\le1$. Let $s>0$. Then there is $c\in c_{00}(V)$ vanishing on $H$ with $\|c\|\le1$ and
--   $$
--   \|f+s(c+k)\|\le\sqrt{1+12s^2}\qquad\text{and}\qquad\|f+s(c-k)\|\le\sqrt{1+12s^2}.
--   $$
--
--   This is the norm form of the paired corrected tests. It is used in the dual estimate for the forest space: if $x$ annihilates the finitely supported vectors living off $H$ and $y$ those living on $H$, evaluating $x+y$ and $x-y$ on the two vectors and averaging cancels the contribution of $c$, which leads to $\sqrt{\|x\|^2+\|y\|^2/12}\le\tfrac12\bigl(\|x+y\|+\|x-y\|\bigr)$.
--
--   **Formalization Note** $c_{00}(V)$ with this norm is the type `TestVector V`; the support conditions are `SupportedOn f H` and `SupportedOn k Hᶜ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Completion.lean#L361-L380

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion

open OAI OAI.ForestSpace OAI.ForestSpace.TestVector
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type}
variable [PartialOrder V]

theorem OAI.ForestSpace.TestVector.paired_correction (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Set V) (hH : IsLowerSet H) (f k : TestVector V)
    (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    (hf₁ : ‖f‖ ≤ 1) (hk₁ : ‖k‖ ≤ 1) (s : ℝ) (hs : 0 < s) :
    ∃ c : TestVector V, SupportedOn c Hᶜ ∧ ‖c‖ ≤ 1 ∧
      ‖f + s • (c + k)‖ ≤ Real.sqrt (1 + 12 * s ^ 2) ∧
      ‖f + s • (c - k)‖ ≤ Real.sqrt (1 + 12 * s ^ 2) := by sorry
