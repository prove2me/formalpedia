-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_exists_injective_not_dense_image_deriv_ne_zero
-- name    : OAI.DirectCrouzeix.Conformal.exists_injective_not_dense_image_deriv_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:59:11.737153+00:00
-- url     : https://prove2.me/theorems/a6bc9545-8a63-48b4-9ca1-412f014bd5e5
-- title:
--   A proper simply connected open subset of $\mathbb{C}$ has an injective map with nonvanishing derivative and non-dense image
-- statement:
--   Let $U\subseteq\mathbb{C}$ be a simply connected open set with $U\neq\mathbb{C}$ (simply connected includes nonempty and path-connected). Then there is a function $f:\mathbb{C}\to\mathbb{C}$ such that
--
--   1. $f$ is injective on all of $\mathbb{C}$;
--   2. the image $f(U)$ is not dense in $\mathbb{C}$;
--   3. $f$ is complex differentiable at every point of $U$ with $f'(z)\neq0$.
--
--   In formulas,
--   $$
--   \exists f:\mathbb{C}\to\mathbb{C}:\quad f\ \text{injective},\qquad \overline{f(U)}\neq\mathbb{C},\qquad f'(z)\neq0\ \ \text{for all } z\in U .
--   $$
--
--   This is the square-root step of Koebe's proof of the Riemann mapping theorem. Since $f(U)$ misses a closed disc $\{|w-w_0|\le\varepsilon\}$ with $\varepsilon>0$, the map $z\mapsto\varepsilon/(f(z)-w_0)$ is an injective holomorphic map of $U$ into the unit disc with nonvanishing derivative; in the development this produces normalized embeddings of $U$ into the unit disc, among which an extremal one is then selected.
--
--   **Formalization Note** The derivative is Lean's `deriv f z`, which is $0$ at points where $f$ is not differentiable; so $f'(z)\neq0$ already forces complex differentiability at every $z\in U$. Off $U$ the function $f$ is otherwise unconstrained; injectivity is required on all of $\mathbb{C}$. Simple connectivity is Mathlib's `IsSimplyConnected U`, which includes nonemptiness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/ExtremalEmbedding.lean#L45-L95

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExtremalEmbedding

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Function Complex
open scoped Pointwise

theorem OAI.DirectCrouzeix.Conformal.exists_injective_not_dense_image_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, Injective f ∧ ¬Dense (f '' U) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by sorry
