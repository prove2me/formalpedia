-- Prove2me | Theorems.Thm_OAI_FiniteCircle_circleCost_order_lower
-- name    : OAI.FiniteCircle.circleCost_order_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:28:57.133203+00:00
-- url     : https://prove2.me/theorems/3ea06ed9-4f83-488b-ad5e-8915b76bb9da
-- title:
--   A nonzero element of $\mathbb{Z}/M$ killed by $q$ lies at circular distance at least $M/q$ from $0$
-- statement:
--   Let $M\ge1$ and consider the cyclic group $\mathbb{Z}/M\mathbb{Z}$. For $x\in\mathbb{Z}/M\mathbb{Z}$ let $\|x\|_M$ be its circular distance to $0$, the least value of $|r|$ over integers $r$ with $r\equiv x\pmod M$; thus $\|x\|_M\in\{0,1,\dots,\lfloor M/2\rfloor\}$. The circle cost of $x$ is the normalised distance
--   $$
--   \operatorname{cost}(x)=\frac{\|x\|_M}{M}\in\Bigl[0,\tfrac12\Bigr],
--   $$
--   which is the distance from $x/M$ to the nearest integer when $x$ is viewed as the point $x/M$ of the circle $\mathbb{R}/\mathbb{Z}$.
--
--   **Theorem.** Let $q\ge1$ be an integer and let $x\in\mathbb{Z}/M\mathbb{Z}$ satisfy $x\neq0$ and $q\,x=0$. Then
--   $$
--   q\cdot\operatorname{cost}(x)\ge1,\qquad\text{equivalently}\qquad \|x\|_M\ge\frac{M}{q}.
--   $$
--
--   Nonzero elements of small order cannot be close to $0$ on the circle. In the lower-bound argument it is applied to nonzero phases assembled from subcircles of prime orders: such a phase is annihilated by the product $Q$ of the primes involved, so its circle cost is at least $1/Q$.
--
--   **Formalization Note** The circle cost is `circleCost x = (x.valMinAbs.natAbs : Real) / M`, where `ZMod.valMinAbs` is the representative of least absolute value; `M` carries a `NeZero` instance, and $q\,x$ is the natural-number multiple `q • x`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/PhaseCost.lean#L45-L61

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.circleCost_order_lower {M q : ℕ} [NeZero M] {x : ZMod M}
    (hq : 0 < q) (hx : x ≠ 0) (hqx : q • x = 0) : 1 ≤ (q : ℝ)*circleCost x := by sorry
