-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Multigraded_product_simple_point_bound_multichart
-- name    : OAI.PermanentBorder.Multigraded.product_simple_point_bound_multichart
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:29:35.898954+00:00
-- url     : https://prove2.me/theorems/efdcf393-fb7e-4fe0-9f4c-8286728ed536
-- title:
--   Simple common zeros seen in local charts are bounded by a multihomogeneous Bézout number
-- statement:
--   **Setting.** Let $\iota$ be a finite set of blocks and $a\in\mathbb{N}^\iota$, and let $R=\mathbb{C}[x_{j,h} : j\in\iota,\ 0\le h\le a_j]$ be multigraded by $\mathbb{Z}^\iota$ with $x_{j,h}$ of multidegree $\mathbf e_j$ (homogeneous coordinates on $\prod_j\mathbb{P}^{a_j}$). Write $\Sigma_a$ for the set of variables and, for $s\in\mathbb{C}$, $\lambda_j(s)=\sum_{h=0}^{a_j}s^hx_{j,h}$. Two points $y,y'\in\mathbb{C}^{\Sigma_a}$ are *block-separated* if $y_{j,h}\,y'_{j,h'}\neq y_{j,h'}\,y'_{j,h}$ for some block $j$ and some $h,h'$, i.e. their coordinate vectors are not proportional in block $j$.
--
--   **Data.**
--   - Factor pairs $(\ell_k,r_k)$, $k=1,\dots,M$: polynomials $\ell_k,r_k$ that are multihomogeneous of recorded multidegrees $\delta_k,\delta'_k\in\mathbb{Z}^\iota$, together with $u,v:\{1,\dots,M\}\to\iota$ and an injective $t:\{1,\dots,M\}\times\{0,1\}\to\mathbb{C}$ such that $\ell_k=\lambda_{u_k}(t_{k,0})$ and $r_k=\lambda_{v_k}(t_{k,1})$, all entries of all $\delta_k$ are at most $1$, and $M=\sum_ja_j$.
--   - Polynomials $F_1,\dots,F_M\in R$, with $F_k$ multihomogeneous of multidegree $\delta_k+\delta'_k$.
--   - A finite set $L$, a complex Banach space $V$, and for each $i\in L$: a continuous linear isomorphism $e_i:\mathbb{C}^M\to V$, a $C^1$ map $\kappa_i:V\to\mathbb{C}^{\Sigma_a}$ (a chart), variables $b_{ij}\in\Sigma_a$ in block $j$ ($j\in\iota$) with $\kappa_i(z)_{b_{ij}}=1$ for all $z\in V$, and a point $x_i\in V$.
--
--   **Hypotheses.** For $i\neq i'$ the points $\kappa_i(x_i)$ and $\kappa_{i'}(x_{i'})$ are block-separated; $F_k(\kappa_i(x_i))=0$ for all $i$ and $k$; and for every $i$ the map
--   $$G_i:V\to V,\qquad G_i(z)=e_i\bigl(F_1(\kappa_i(z)),\dots,F_M(\kappa_i(z))\bigr),$$
--   has invertible derivative at $x_i$.
--
--   **Conclusion.**
--   $$|L|\ \le\ [X^a]\prod_{k=1}^M\bigl(X_{u_k}+X_{v_k}\bigr),$$
--   the coefficient of $\prod_jX_j^{a_j}$ in the product, computed in $\mathbb{N}[X_j : j\in\iota]$.
--
--   So the system $F_1=\dots=F_M=0$ has at most as many simple zeros on $\prod_j\mathbb{P}^{a_j}$ as its multihomogeneous Bézout number, where each zero may be presented in its own chart and simplicity is tested in that chart. Allowing a separate chart per point makes the count applicable to zeros produced by local constructions, such as kernel vectors of matrices.
--
--   **Formalization Note** $\Sigma_a$ is `BlockVariables a = Σ j, Fin (a j + 1)` and $\lambda_j(s)$ is `blockLinearForm a j s`; the pairs form a list `qs` of `FactorPair` structures indexed by `Fin qs.length` (so $k$ runs over $0,\dots,M-1$). The chart $\kappa_i$ is `chart i` with `ContDiff ℂ 1`, invertibility of the derivative is `(fderiv ℂ _ (x i)).IsInvertible`, block separation is `BlockSeparated`, and the bound compares `Fintype.card L` with the coefficient of `mixedPolynomial u v` at `a`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/ProjectiveCounts.lean#L285-L364

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts

open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem OAI.PermanentBorder.Multigraded.product_simple_point_bound_multichart (a : ι →₀ ℕ)
    (qs : List (FactorPair (K := ℂ) (blockWeight (fun v : BlockVariables a => v.1))))
    (u v : Fin qs.length → ι) (t : (Fin qs.length × Bool) → ℂ)
    (ht : Function.Injective t)
    (hleft : ∀ i, (qs.get i).left = blockLinearForm a (u i) (t (i,false)))
    (hright : ∀ i, (qs.get i).right = blockLinearForm a (v i) (t (i,true)))
    (hdeg : ∀ q ∈ qs, ∀ j, q.leftDegree j ≤ 1)
    (hlen : qs.length = ∑ j, a j)
    (F : Fin qs.length → MvPolynomial (BlockVariables a) ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      ((qs.get i).leftDegree + (qs.get i).rightDegree))
    (base : L → ι → BlockVariables a) (hbase : ∀ i j, (base i j).1 = j)
    (e : L → (Fin qs.length → ℂ) ≃L[ℂ] V)
    (chart : L → V → BlockVariables a → ℂ) (hc : ∀ i, ContDiff ℂ 1 (chart i))
    (hcn : ∀ i z j, chart i z (base i j) = 1)
    (x : L → V)
    (hx : ∀ i j, i ≠ j → BlockSeparated (fun v : BlockVariables a => v.1)
      (chart i (x i)) (chart j (x j)))
    (hz : ∀ i j, eval (chart i (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z => e i (fun j => eval (chart i z) (F j)))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by sorry
