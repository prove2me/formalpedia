-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_constant_or_injective_limit
-- name    : OAI.DirectCrouzeix.Conformal.constant_or_injective_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:57:14.08356+00:00
-- url     : https://prove2.me/theorems/a876cd83-403a-4ac1-a102-72b5b4acc9d6
-- title:
--   A locally uniform limit of injective holomorphic functions is constant or injective
-- statement:
--   Let $U\subseteq\mathbb{C}$ be an open preconnected set, for instance a domain. Let $F_n:\mathbb{C}\to\mathbb{C}$ $(n\in\mathbb{N})$ be functions that are holomorphic on $U$ and injective on $U$, and let $g:\mathbb{C}\to\mathbb{C}$ be such that $F_n\to g$ locally uniformly on $U$ as $n\to\infty$. Then $g$ is constant on $U$ or injective on $U$:
--   $$
--   \exists\,c\in\mathbb{C}\ \ \forall z\in U:\ g(z)=c\qquad\text{or}\qquad\forall z,w\in U:\ g(z)=g(w)\implies z=w .
--   $$
--
--   This is the classical consequence of Hurwitz's theorem for univalent functions. In the development it shows that a limit of normalized injective embeddings of a simply connected domain into the unit disc, whose derivative at the base point is nonzero, is again injective; this is a step in the construction of an extremal embedding.
--
--   **Formalization Note** Holomorphy on $U$ is `DifferentiableOn ℂ (F n) U`, injectivity is `InjOn (F n) U`, and the convergence is `TendstoLocallyUniformlyOn F g atTop U`. Only the values of $F_n$ and $g$ on $U$ matter.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/NormalFamilies.lean#L86-L118

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

theorem OAI.DirectCrouzeix.Conformal.constant_or_injective_limit {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hFi : ∀ n, InjOn (F n) U)
    (hl : TendstoLocallyUniformlyOn F g atTop U) :
    (∃ c : ℂ, EqOn g (fun _ => c) U) ∨ InjOn g U := by sorry
