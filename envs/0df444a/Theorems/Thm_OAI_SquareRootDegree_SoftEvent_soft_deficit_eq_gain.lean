-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_SoftEvent_soft_deficit_eq_gain
-- name    : OAI.SquareRootDegree.SoftEvent.soft_deficit_eq_gain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:54:16.988076+00:00
-- url     : https://prove2.me/theorems/68acafc2-57d1-4abd-8539-fbbe9a6306f3
-- title:
--   The deficit of a soft switching event equals the moment gain functional
-- statement:
--   Let $\iota$ be a finite index set and $\alpha$ a finite nonempty set, and write $\mathbb E$ for uniform averages over finite sets. Let $T:\alpha\to\mathbb R$ be standardised, $\mathbb E_aT(a)=0$ and $\mathbb E_aT(a)^2=1$. Let $w_i,s_i:\alpha\to\mathbb R$ ($i\in\iota$) be two families of weights (leaf weights and selector weights) with $\mathbb E_a w_i(a)\neq0$ for every $i$. Their raw moments against $T$ are
--   $$l_k(i)=\mathbb E_a\big[w_i(a)\,T(a)^k\big],\qquad m_k(i)=\mathbb E_a\big[s_i(a)\,T(a)^k\big],\qquad k=0,1,2,$$
--   and the leaf moments define weighted means and variances $\bar\mu_i=l_1(i)/l_0(i)$ and $\bar v_i=l_2(i)/l_0(i)-\bar\mu_i^2$.
--
--   On the product set of points $(u,z)\in\alpha\times\alpha^\iota$ (a fresh coordinate $u$ and old coordinates $z=(z_j)_{j\in\iota}$), define the soft switching weight
--   $$A(u,z)=\sum_{i\in\iota}s_i(u)\prod_{j\neq i}w_j(z_j)-\prod_{j\in\iota}w_j(z_j),$$
--   and, for a shift $b\in\mathbb R$, the deficit $D_b=\mathbb E_{(u,z)}\Big[A(u,z)\Big(1-\big(T(u)+\sum_{j}T(z_j)-b\big)^2\Big)\Big]$, the average being uniform over $\alpha\times\alpha^\iota$. Then, for the shift $b=\sum_i\bar\mu_i-1$,
--
--   $$
--   D_b=\Big(\prod_i l_0(i)\Big)\Big(1+\sum_i\bar v_i-\sum_i\frac{m_2(i)+2(1-\bar\mu_i)\,m_1(i)+\big((1-\bar\mu_i)^2+\sum_{j\neq i}\bar v_j\big)\,m_0(i)}{l_0(i)}\Big).
--   $$
--
--   The right-hand side is the gain functional $\mathcal G(l,m)$; it depends only on the moments of order at most two of the single-coordinate weights. When the $s_i$ and $w_i$ take values in $\{0,1\}$ and exactly one $s_i(u)$ equals $1$ for each $u$, $A$ is the indicator of the event that the leaf selected by $u$ fails its test at its old coordinate while every other old coordinate passes its test, so the identity evaluates the deficit of a genuine switching event in closed form.
--
--   **Formalization Note** The moments, weight, deficit and gain are `rawMoments T w`, `softWeight s w`, `deficit T b` and `gain`, with `means` and `vars` as above; products over $j\neq i$ run over `Finset.univ.erase i`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/SoftEvent.lean#L136-L187

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent

open OAI OAI.SquareRootDegree OAI.SquareRootDegree.SoftEvent
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
attribute [local instance] Classical.propDecidable
open MomentTransfer
variable {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]

theorem OAI.SquareRootDegree.SoftEvent.soft_deficit_eq_gain (s w : ι → α → ℝ) (hw : ∀ i, average (w i) ≠ 0)
    (T : α → ℝ) (h0 : average T = 0) (h1 : average (fun a => (T a)^2) = 1) :
    deficit T ((∑ i, means (rawMoments T w) i)-1) (softWeight s w) =
      gain (rawMoments T w) (rawMoments T s) := by sorry
