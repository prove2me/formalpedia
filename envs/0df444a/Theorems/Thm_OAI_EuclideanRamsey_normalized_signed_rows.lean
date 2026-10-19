-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_normalized_signed_rows
-- name    : OAI.EuclideanRamsey.normalized_signed_rows
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:18:40.295688+00:00
-- url     : https://prove2.me/theorems/1b0c1de8-a14c-462f-9733-8507242c0e0b
-- title:
--   Normalizing a signed rational measure into two value-matched families of affine rows
-- statement:
--   Let $X$ be a set, let $s\ge1$ and $d\ge0$ be integers, and let $a_1,\dots,a_s\in\mathbb R^d$. Let $v:X\to\mathbb R$ and $g=(g_1,\dots,g_d):X\to\mathbb R^d$ be functions, let $f:X\to\mathbb Q$ be finitely supported, and let $\zeta>0$ and $\eta$ be real numbers. For $x\in X$ write $\lambda_i(x)=v(x)+\sum_{j=1}^da_{ij}\,g_j(x)$. Assume
--
--   1. (balanced evaluations) for each $i$ and each $t\in\mathbb R$, $\displaystyle\sum_{x:\ \lambda_i(x)=t}f(x)=0$;
--   2. (isotropic second moments) $\displaystyle\sum_{x}f(x)\,g_j(x)\,g_l(x)=\zeta\,\delta_{jl}$ for all $1\le j,l\le d$;
--   3. (small negative part) $\displaystyle\sum_{x}\max\bigl(-f(x),0\bigr)\,|g(x)|^2<\eta\,\zeta$, where $|g(x)|^2=\sum_jg_j(x)^2$.
--
--   Then there are a finite index set $T$, functions $v^+,v^-:T\to\mathbb R$ and real $d\times T$ matrices $U,V$ such that
--   $$UU^{\top}-VV^{\top}=I_d,\qquad\operatorname{tr}\bigl(VV^{\top}\bigr)<\eta,$$
--   and for every $i$ there is a permutation $\sigma_i$ of $T$ with
--   $$v^-(\sigma_i(x))+\sum_{j=1}^da_{ij}\,V_{j,\sigma_i(x)}=v^+(x)+\sum_{j=1}^da_{ij}\,U_{jx}\qquad\text{for all }x\in T .$$
--
--   Each column $x$ gives an affine function $y\mapsto v^+(x)+\sum_jy_jU_{jx}$ (and similarly with $v^-,V$) on $\mathbb R^d$. The conclusion says that at every point $a_i$ the "positive" and the "negative" family take the same multiset of values, their Gram matrices differ by exactly the identity, and the negative family is small in trace. This is the matrix form of the near-positive signed measure produced by the smoothing step, and it is the input for the construction of two-scale embeddings.
--
--   **Formalization Note** $X$ is a type `α` with decidable equality and $f$ is a finitely supported function `α →₀ ℚ`; hypothesis 1 is `f.mapDomain λ_i = 0` and the sums are `Finsupp.sum`. The points $a_i$ are plain functions `Fin d → ℝ`, and $T$ is a type with a `Fintype` instance. No sign condition on $\eta$ is imposed (hypothesis 3 forces $\eta>0$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/SignedRows.lean#L158-L230

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows

open OAI OAI.EuclideanRamsey
universe uAlpha uBeta
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators
open Matrix

theorem OAI.EuclideanRamsey.normalized_signed_rows {α : Type} [DecidableEq α] {d s : ℕ} (hs : 0 < s)
    (a : Fin s → Fin d → ℝ) (v : α → ℝ) (g : α → Fin d → ℝ)
    (f : α →₀ ℚ) (ζ η : ℝ) (hζ : 0 < ζ)
    (heval : ∀ i,f.mapDomain (fun x => v x+∑ j,a i j*g x j)=0)
    (hmom : ∀ j l,f.sum (fun x q => (q:ℝ)*g x j*g x l)=ζ*(if j=l then 1 else 0))
    (hneg : f.sum (fun x q => max (-(q:ℝ)) 0*(∑ j,(g x j)^2)) < η*ζ) :
    ∃ (τ : Type) (_ : Fintype τ) (vp vn : τ → ℝ) (U V : Matrix (Fin d) τ ℝ),
      U*U.transpose-V*V.transpose=1 ∧ (V*V.transpose).trace < η ∧
      ∀ i,∃ σ : Equiv.Perm τ,∀ x,
        vn (σ x)+∑ j,a i j*V j (σ x) = vp x+∑ j,a i j*U j x := by sorry
