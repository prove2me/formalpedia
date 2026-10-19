-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_permutation_equal_endpoints
-- name    : OAI.EuclideanRamsey.permutation_equal_endpoints
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:46:13.234414+00:00
-- url     : https://prove2.me/theorems/d754b977-e639-4543-ab2c-da5ba8ea54f2
-- title:
--   Permuted two-scale copies give one word tuple with path weights of ratio at most $q+s\delta$
-- statement:
--   Let $E=\mathbb{R}^{(\mathbb{N})}$ be the real inner-product space of finitely supported real sequences $x=(x_0,x_1,\dots)$ with $\langle x,y\rangle=\sum_{n}x_ny_n$, and for $k\in\mathbb{N}$ let $\iota_k:\mathbb{R}^k\to E$ be the linear isometry that copies the $k$ coordinates of a vector into positions $0,\dots,k-1$ and pads with zeros. Let $F(E)$ be the free group whose letters are the points of $E$, and write $[x]\in F(E)$ for the generator attached to $x\in E$.
--
--   For a configuration $\tilde a=(\tilde a_0,\dots,\tilde a_{s-1})$ of points of $E$, *path weights* are defined inductively on tuples $w=(w_0,\dots,w_{s-1})\in F(E)^s$: we write $w\in\mathrm{Path}_{\tilde a}(\lambda)$, and say that $w$ is a path of weight $\lambda\in\mathbb{R}$, if this follows from the rules
--
--   1. (constant tuples) for every $h\in F(E)$, the tuple $(h,\dots,h)$ is a path of weight $0$;
--   2. (scaled copies) if $u\ge0$ and $b_0,\dots,b_{s-1}\in E$ satisfy $\|b_i-b_j\|^2=u\,\|\tilde a_i-\tilde a_j\|^2$ for all $i,j$, then $([b_0],\dots,[b_{s-1}])$ is a path of weight $u$;
--   3. (products) if $w$ is a path of weight $\lambda$ and $v$ is a path of weight $\mu$, then the coordinatewise product $(w_0v_0,\dots,w_{s-1}v_{s-1})$ is a path of weight $\lambda+\mu$.
--
--   The same tuple can be a path of several different weights.
--
--   **Theorem.** Let $s,d,\ell\in\mathbb{N}$, let $a_0,\dots,a_{s-1}\in\mathbb{R}^d$ be pairwise distinct, and let $q>0$ and $\delta>0$ be real numbers. Let $f_0,\dots,f_{s-1}$ and $g_0,\dots,g_{s-1}$ be points of $\mathbb{R}^\ell$ such that
--
--   $$
--   \|f_i-f_j\|^2=\|a_i-a_j\|^2\quad\text{and}\quad\|g_i-g_j\|^2=q\,\|a_i-a_j\|^2\qquad\text{for all } i,j,
--   $$
--
--   and such that each $g_i$ is a coordinate permutation of $f_i$: for every $i$ there is a permutation $\sigma_i$ of $\{0,\dots,\ell-1\}$ with $(g_i)_{\sigma_i(x)}=(f_i)_x$ for all $x$. Put $\tilde a_i=\iota_d(a_i)$. Then there exist a tuple $w\in F(E)^s$ and real numbers $\lambda,\mu$ with
--
--   $$
--   w\in\mathrm{Path}_{\tilde a}(\lambda),\qquad w\in\mathrm{Path}_{\tilde a}(\mu),\qquad \lambda>0,\qquad \mu\ge0,\qquad \frac{\mu}{\lambda}\le q+s\,\delta.
--   $$
--
--   In words: $f$ is a congruent copy of $a$, and $g$ is a copy of $a$ scaled by $\sqrt q$ whose points are coordinate rearrangements of the corresponding points of $f$. The theorem converts this into a single tuple of words that can be assembled from scaled copies of $\tilde a$ in two ways whose total weights have ratio at most $q+s\delta$, where $\delta>0$ is arbitrary. In the classification of Ramsey configurations it is applied with small $q$ to produce, for every $n\ge1$, a tuple with two path weights of ratio less than $1/n$; such tuples are the input of the argument that produces monochromatic congruent copies.
--
--   **Formalization Note** Points of $\mathbb{R}^k$ are elements of `EuclideanSpace ℝ (Fin k)`, so all indices run over $\{0,\dots,k-1\}$, and pairwise distinctness is `Function.Injective a`. The space $E$ is `FiniteEuclidean` (the type `ℕ →₀ ℝ` with the $\ell^2$ inner product), $\iota_k$ is `FiniteEuclidean.embed k`, $F(E)$ is `LetterGroup` (`FreeGroup FiniteEuclidean`), and $w\in\mathrm{Path}_{\tilde a}(\lambda)$ is the inductive predicate `Path (fun i => FiniteEuclidean.embed d (a i)) w lmb`; the scaled-copy rule is phrased through `CopyPath`, which records $u\ge0$ explicitly. Since $\lambda>0$ is part of the conclusion, the quotient $\mu/\lambda$ is an honest real division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CorrectionPaths.lean#L174-L218

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
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths

open OAI OAI.EuclideanRamsey
universe uGroup uIndex uAction uPoint
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
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set
open scoped BigOperators

theorem OAI.EuclideanRamsey.permutation_equal_endpoints {s d ℓ : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin d))
    (ha : Function.Injective a) (f g : Fin s → EuclideanSpace ℝ (Fin ℓ))
    (q δ : ℝ) (hq : 0 < q) (hδ : 0 < δ)
    (hf : ∀ i j,‖f i-f j‖^2=‖a i-a j‖^2)
    (hg : ∀ i j,‖g i-g j‖^2=q*‖a i-a j‖^2)
    (hperm : ∀ i,∃ σ : Equiv.Perm (Fin ℓ),∀ x,g i (σ x)=f i x) :
    ∃ w lmb μ,Path (fun i => FiniteEuclidean.embed d (a i)) w lmb ∧
      Path (fun i => FiniteEuclidean.embed d (a i)) w μ ∧ 0 < lmb ∧ 0 ≤ μ ∧ μ/lmb ≤ q+s*δ := by sorry
