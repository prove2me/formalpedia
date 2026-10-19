-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_ramsey_realCriterion
-- name    : OAI.EuclideanRamsey.ramsey_realCriterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T01:56:31.672011+00:00
-- url     : https://prove2.me/theorems/5acccef2-2578-4e86-af99-41c783727bf4
-- title:
--   Ramsey configurations satisfy the real tensor criterion
-- statement:
--   Let $s\ge 1$ and $d$ be natural numbers and let $a=(a_0,\dots,a_{s-1})$ be points of Euclidean space $\mathbb{R}^d$ whose affine span is all of $\mathbb{R}^d$.
--
--   *Ramsey property.* The configuration $a$ is Ramsey if for every number of colours $r\ge 2$ there is a dimension $D\ge 1$ such that every colouring $c:\mathbb{R}^D\to\{0,\dots,r-1\}$ admits points $b_0,\dots,b_{s-1}\in\mathbb{R}^D$ with $\|b_i-b_j\|=\|a_i-a_j\|$ for all $i,j$ and $c(b_0)=c(b_1)=\dots=c(b_{s-1})$.
--
--   *Real criterion.* Let $T=\mathbb{R}\otimes_{\mathbb{Q}}\mathbb{R}$ be the tensor product of $\mathbb{R}$ with itself over $\mathbb{Q}$ (a commutative ring), and $\mu:T\to\mathbb{R}$ the multiplication map, $\mu(x\otimes y)=xy$. Index rows and columns by the augmented set $\{\ast,1,\dots,d\}$ and let $\hat a_i=(\hat a_i(\ast),\hat a_i(1),\dots,\hat a_i(d))=(1,a_{i1},\dots,a_{id})$ be the augmented coordinate vector of $a_i$. The configuration satisfies the real criterion if there is a matrix $P=(P_{\alpha\beta})$ with entries in $T$, indexed by the augmented set, such that
--   $$\sum_{\alpha,\beta}\bigl(\hat a_i(\alpha)\otimes 1\bigr)\,P_{\alpha\beta}\,\bigl(1\otimes\hat a_i(\beta)\bigr)=0\quad(0\le i<s),\qquad \mu(P_{\alpha\beta})=\delta_{\alpha\beta}\quad(1\le\alpha,\beta\le d).$$
--
--   **Theorem.** If $a$ is Ramsey, then $a$ satisfies the real criterion.
--
--   This is the necessity half of the classification of Ramsey configurations: together with a descent of the certificate $P$ from $\mathbb{R}\otimes_{\mathbb{Q}}\mathbb{R}$ to $K\otimes_{\mathbb{Q}}K$, where $K$ is the field generated over $\mathbb{Q}$ by the coordinates of the $a_i$, it shows that every Ramsey configuration satisfies the field criterion.
--
--   **Formalization Note** `Space d` is `EuclideanSpace ℝ (Fin d)`. `Ramsey a` quantifies over colourings `Space D → Fin r` and uses `dist` for congruence. The augmented index set is `Option (Fin d)` with `none` in the role of $\ast$; `RealCriterion a` asks for `P : RealArray d` with `arrayEvaluation a i P = 0` for all `i` and `spatialMultiply P = 1`, where `spatialMultiply` applies `Algebra.TensorProduct.lmul' ℚ` to the entries indexed by `some α, some β`. The hypothesis $s\ge1$ is `0 < s`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/TensorNecessity.lean#L227-L256

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity

open OAI OAI.EuclideanRamsey
universe uPoint
open scoped TensorProduct RealInnerProductSpace

theorem OAI.EuclideanRamsey.ramsey_realCriterion {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hR : Ramsey a) : RealCriterion a := by sorry
