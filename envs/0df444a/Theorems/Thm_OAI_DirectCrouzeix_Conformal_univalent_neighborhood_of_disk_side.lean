-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_univalent_neighborhood_of_disk_side
-- name    : OAI.DirectCrouzeix.Conformal.univalent_neighborhood_of_disk_side
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:13:25.76339+00:00
-- url     : https://prove2.me/theorems/bb07ea49-4fe2-4893-b48b-870ae99e343a
-- title:
--   Univalence on a neighbourhood of $\overline{U}$ for an analytic map of $U$ onto the unit disk
-- statement:
--   Let $U,V\subseteq\mathbb{C}$ be sets such that $V$ is open, $\overline{U}\subseteq V$, and the closure $\overline{U}$ is compact (so $U$ is bounded; $U$ itself is not assumed to be open). Write $\mathbb{D}=\{w\in\mathbb{C}:|w|<1\}$ and $\overline{\mathbb{D}}=\{w\in\mathbb{C}:|w|\le1\}$. Let $F:\mathbb{C}\to\mathbb{C}$ be a function such that
--
--   1. $F$ is analytic at every point of $V$;
--   2. $F$ is injective on $U$ and $F(U)=\mathbb{D}$;
--   3. for every $z\in V$, one has $|F(z)|<1$ if and only if $z\in U$;
--   4. $F'(p)\neq0$ for every $p\in\overline{U}$.
--
--   Then there is an open set $W\subseteq\mathbb{C}$ such that
--
--   $$
--   \overline{U}\subseteq W\subseteq V,\qquad F|_{W}\ \text{is injective},\qquad F\ \text{is analytic at every point of } W,\qquad F(\overline{U})=\overline{\mathbb{D}}.
--   $$
--
--   Thus a map that sends $U$ bijectively onto the unit disk, is analytic on a neighbourhood $V$ of $\overline{U}$ with nonvanishing derivative on $\overline{U}$, and has modulus less than $1$ on $V$ exactly at the points of $U$, is univalent on a whole neighbourhood of $\overline{U}$ and maps $\overline{U}$ onto the closed disk. Applied to the analytic continuation of a Riemann map, it makes the inverse map available on a disk of radius larger than $1$.
--
--   **Formalization Note** Injectivity on a set is `InjOn`, analyticity on a set is `AnalyticOnNhd ℂ` (analyticity at each point), and $F'(p)$ is Lean's `deriv`, the genuine complex derivative since $F$ is analytic at each point of $\overline{U}\subseteq V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/Continuation.lean#L140-L168

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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DiskMapping
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PoissonBoundary
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HarmonicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HolomorphicReflection

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Function Complex
open scoped Pointwise
open InnerProductSpace Real

theorem OAI.DirectCrouzeix.Conformal.univalent_neighborhood_of_disk_side {U V : Set ℂ} (hV : IsOpen V)
    (hUV : closure U ⊆ V) (hUc : IsCompact (closure U))
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F V)
    (hi : InjOn F U) (hm : F '' U = ball 0 1)
    (hside : ∀ z ∈ V, ‖F z‖ < 1 ↔ z ∈ U)
    (hd : ∀ p ∈ closure U, deriv F p ≠ 0) :
    ∃ W, IsOpen W ∧ closure U ⊆ W ∧ W ⊆ V ∧
      InjOn F W ∧ AnalyticOnNhd ℂ F W ∧ F '' closure U = closedBall 0 1 := by sorry
