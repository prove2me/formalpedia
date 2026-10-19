-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_two_scale_of_signed_rows
-- name    : OAI.EuclideanRamsey.two_scale_of_signed_rows
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:19:43.93334+00:00
-- url     : https://prove2.me/theorems/e4d3a1f4-a479-4dee-b302-8036734c21a9
-- title:
--   Signed rows give a congruent copy and a scaled copy whose corresponding points differ by a coordinate permutation
-- statement:
--   Let $d\ge1$ and $s\ge1$, and let $a_1,\dots,a_s$ be points of the Euclidean space $\mathbb R^d$. Let $X$ be a set, let $v:X\to\mathbb R$ and $g=(g_1,\dots,g_d):X\to\mathbb R^d$ be functions, let $f:X\to\mathbb Q$ be finitely supported, and let $\zeta>0$ and $\eta>0$. For $x\in X$ write $\lambda_i(x)=v(x)+\sum_{j=1}^da_{ij}\,g_j(x)$, and assume
--
--   1. (balanced evaluations) for each $i$ and each $t\in\mathbb R$, $\displaystyle\sum_{x:\ \lambda_i(x)=t}f(x)=0$;
--   2. (isotropic second moments) $\displaystyle\sum_{x}f(x)\,g_j(x)\,g_l(x)=\zeta\,\delta_{jl}$ for all $1\le j,l\le d$;
--   3. (small negative part) $\displaystyle\sum_{x}\max\bigl(-f(x),0\bigr)\,|g(x)|^2<\eta\,\zeta$, where $|g(x)|^2=\sum_jg_j(x)^2$.
--
--   Then there exist an integer $\ell\ge1$ and points $p_1,\dots,p_s$ and $q_1,\dots,q_s$ of the Euclidean space $\mathbb R^\ell$ such that for all $i,j$
--   $$|p_i-p_j|^2=|a_i-a_j|^2,\qquad|q_i-q_j|^2=\frac{\eta}{1+\eta}\,|a_i-a_j|^2,$$
--   and for every $i$ there is a permutation $\sigma_i$ of the coordinate set $\{1,\dots,\ell\}$ with $q_i(\sigma_i(x))=p_i(x)$ for every coordinate $x$.
--
--   Thus $p$ is congruent to $a$, $q$ is a copy of $a$ scaled by $\sqrt{\eta/(1+\eta)}$, and each point $q_i$ is obtained from $p_i$ by permuting coordinates (so $p_i$ and $q_i$ have the same multiset of coordinates). Since $\eta/(1+\eta)$ can be made as small as desired, this two-scale structure is the geometric input used to show that configurations satisfying the field criterion are Ramsey.
--
--   **Formalization Note** $X$ is a type `α` with decidable equality, $f$ is `α →₀ ℚ`, hypothesis 1 is `f.mapDomain λ_i = 0`, and the points are elements of `EuclideanSpace ℝ (Fin d)` and `EuclideanSpace ℝ (Fin ℓ)`; coordinates are indexed by `Fin ℓ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/GramCompletion.lean#L123-L178

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
universe uIndex uRow uColor
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
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Matrix

theorem OAI.EuclideanRamsey.two_scale_of_signed_rows {α : Type} [DecidableEq α] {d s : ℕ}
    (hd : 0 < d) (hs : 0 < s) (a : Fin s → EuclideanSpace ℝ (Fin d))
    (v : α → ℝ) (g : α → Fin d → ℝ) (f : α →₀ ℚ)
    (ζ η : ℝ) (hζ : 0 < ζ) (hη : 0 < η)
    (heval : ∀ i,f.mapDomain (fun x => v x+∑ j,a i j*g x j)=0)
    (hmom : ∀ j l,f.sum (fun x q => (q:ℝ)*g x j*g x l)=ζ*(if j=l then 1 else 0))
    (hneg : f.sum (fun x q => max (-(q:ℝ)) 0*(∑ j,(g x j)^2)) < η*ζ) :
    ∃ (ℓ : ℕ),1 ≤ ℓ ∧ ∃ (f' g' : Fin s → EuclideanSpace ℝ (Fin ℓ)),
      (∀ i j,‖f' i-f' j‖^2=‖a i-a j‖^2) ∧
      (∀ i j,‖g' i-g' j‖^2=(η/(1+η))*‖a i-a j‖^2) ∧
      ∀ i,∃ σ : Equiv.Perm (Fin ℓ),∀ x,g' i (σ x)=f' i x := by sorry
