-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_zero_or_nonvanishing_limit
-- name    : OAI.DirectCrouzeix.Conformal.zero_or_nonvanishing_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:56:06.225189+00:00
-- url     : https://prove2.me/theorems/c2c36f3f-866d-498f-9b1c-35f2b9acc41b
-- title:
--   Hurwitz's theorem: a locally uniform limit of zero-free holomorphic functions is zero-free or identically zero
-- statement:
--   Let $U\subseteq\mathbb{C}$ be an open preconnected set, for instance a domain. Let $F_n:\mathbb{C}\to\mathbb{C}$ $(n\in\mathbb{N})$ be functions that are holomorphic on $U$ and have no zeros in $U$, and let $g:\mathbb{C}\to\mathbb{C}$ be such that $F_n\to g$ locally uniformly on $U$ as $n\to\infty$, i.e. every point of $U$ has a neighbourhood in $U$ on which $F_n\to g$ uniformly. Then
--   $$
--   g(z)=0\ \text{ for all } z\in U\qquad\text{or}\qquad g(z)\neq0\ \text{ for all } z\in U .
--   $$
--
--   This is a form of Hurwitz's theorem on the zeros of limits of holomorphic functions. In the development it is applied to the derivatives of a convergent sequence of injective holomorphic maps, to show that the derivative of the limit map does not vanish, and it is also the key step in showing that non-constant limits of injective holomorphic maps are injective.
--
--   **Formalization Note** Holomorphy on $U$ is `DifferentiableOn ℂ (F n) U`, which for open $U$ means complex differentiability at every point of $U$, and the convergence is `TendstoLocallyUniformlyOn F g atTop U`. Only the values of $F_n$ and $g$ on $U$ matter. Preconnectedness allows $U=\emptyset$, in which case both alternatives hold.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/NormalFamilies.lean#L27-L84

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
universe u_131
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate

theorem OAI.DirectCrouzeix.Conformal.zero_or_nonvanishing_limit {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hFn : ∀ n z, z ∈ U → F n z ≠ 0)
    (hl : TendstoLocallyUniformlyOn F g atTop U) :
    EqOn g 0 U ∨ ∀ z ∈ U, g z ≠ 0 := by sorry
