-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Multigraded_bilinear_simple_point_count_multichart
-- name    : OAI.PermanentBorder.Multigraded.bilinear_simple_point_count_multichart
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:30:59.254919+00:00
-- url     : https://prove2.me/theorems/705f6ce1-f5dc-4174-89f5-399b6c4fbfc5
-- title:
--   Bézout bound for simple zeros of forms of multidegree $\mathbf{e}_{u_k}+\mathbf{e}_{v_k}$ on a product of projective spaces
-- statement:
--   Let $\iota$ be a finite set of blocks, $a\in\mathbb{N}^\iota$ and $M=\sum_{j\in\iota}a_j$, and let $R=\mathbb{C}[x_{j,h} : j\in\iota,\ 0\le h\le a_j]$ be multigraded by $\mathbb{Z}^\iota$ with $x_{j,h}$ of multidegree $\mathbf e_j$; write $\Sigma_a$ for the set of variables. Let $u,v:\{1,\dots,M\}\to\iota$ and let $F_1,\dots,F_M\in R$, with $F_k$ multihomogeneous of multidegree $\mathbf e_{u_k}+\mathbf e_{v_k}$ (bilinear in the blocks $u_k$ and $v_k$, or quadratic in one block if $u_k=v_k$). Two points $y,y'\in\mathbb{C}^{\Sigma_a}$ are *block-separated* if $y_{j,h}\,y'_{j,h'}\neq y_{j,h'}\,y'_{j,h}$ for some block $j$ and some $h,h'$.
--
--   Let $L$ be a finite set and $V$ a complex Banach space, and suppose that for every $i\in L$ we are given a continuous linear isomorphism $e_i:\mathbb{C}^M\to V$, a $C^1$ map $\kappa_i:V\to\mathbb{C}^{\Sigma_a}$ (a chart), variables $b_{ij}$ in block $j$ ($j\in\iota$) with $\kappa_i(z)_{b_{ij}}=1$ for all $z\in V$, and a point $x_i\in V$, such that
--   - $\kappa_i(x_i)$ and $\kappa_{i'}(x_{i'})$ are block-separated whenever $i\neq i'$;
--   - $F_k(\kappa_i(x_i))=0$ for all $i$ and $k$;
--   - the map $G_i:V\to V$, $G_i(z)=e_i\bigl(F_1(\kappa_i(z)),\dots,F_M(\kappa_i(z))\bigr)$, has invertible derivative at $x_i$.
--
--   Then
--   $$|L|\ \le\ [X^a]\prod_{k=1}^M\bigl(X_{u_k}+X_{v_k}\bigr),$$
--   the coefficient of $\prod_jX_j^{a_j}$ in the product, computed in $\mathbb{N}[X_j : j\in\iota]$.
--
--   This is the multihomogeneous Bézout bound for simple zeros of $M$ forms of multidegrees $\mathbf e_{u_k}+\mathbf e_{v_k}$ on $\prod_j\mathbb{P}^{a_j}$, in a version where each zero is presented, and tested for simplicity, in its own chart. Systems of this shape arise from kernel equations of matrices, which are bilinear in a left and a right kernel vector; this is how the count enters lower bounds for determinantal representations.
--
--   **Formalization Note** $\Sigma_a$ is `BlockVariables a = Σ j, Fin (a j + 1)` with `a : ι →₀ ℕ`, the multidegree of $F_k$ is `Pi.single (u k) 1 + Pi.single (v k) 1` for the weight `blockWeight`, the index $k$ ranges over `Fin M`, and the bound compares `Fintype.card L` with the coefficient of `mixedPolynomial u v` at `a`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/ProjectiveCounts.lean#L374-L411

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts

open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem OAI.PermanentBorder.Multigraded.bilinear_simple_point_count_multichart (a : ι →₀ ℕ) {M : ℕ}
    (u v : Fin M → ι) (hM : M = ∑ j, a j)
    (F : Fin M → MvPolynomial (BlockVariables a) ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      (Pi.single (u i) 1 + Pi.single (v i) 1))
    (base : L → ι → BlockVariables a) (hbase : ∀ i j, (base i j).1 = j)
    (e : L → (Fin M → ℂ) ≃L[ℂ] V)
    (chart : L → V → BlockVariables a → ℂ) (hc : ∀ i, ContDiff ℂ 1 (chart i))
    (hcn : ∀ i z j, chart i z (base i j) = 1)
    (x : L → V)
    (hx : ∀ i j, i ≠ j → BlockSeparated (fun v : BlockVariables a => v.1)
      (chart i (x i)) (chart j (x j)))
    (hz : ∀ i j, eval (chart i (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z => e i (fun j => eval (chart i z) (F j)))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by sorry
