-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_bounded_holomorphic_compact
-- name    : OAI.DirectCrouzeix.Conformal.bounded_holomorphic_compact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:58:25.12238+00:00
-- url     : https://prove2.me/theorems/00b31468-37b9-4bca-8da5-b62196eb2a9f
-- title:
--   Montel's theorem: holomorphic functions bounded by $1$ form a relatively compact family
-- statement:
--   Let $U\subseteq\mathbb{C}$ be open, and let $C(U,\mathbb{C})$ be the space of continuous functions $U\to\mathbb{C}$ with the compact-open topology, which is the topology of uniform convergence on compact subsets of $U$. Let $S\subseteq C(U,\mathbb{C})$ be a family such that every $f\in S$ is holomorphic on $U$ and satisfies $|f(z)|\le1$ for all $z\in U$. Then the closure of $S$ is compact:
--   $$
--   \overline{S}\ \text{ is a compact subset of } C(U,\mathbb{C}).
--   $$
--
--   This is Montel's theorem for a uniformly bounded family of holomorphic functions: every sequence in $S$ has a subsequence converging uniformly on compact subsets of $U$. In the development it provides the compactness needed to maximize $|f'(a)|$ over the normalized injective embeddings $f$ of a simply connected domain into the unit disc.
--
--   **Formalization Note** $S$ is a set of bundled continuous maps `C(U, ℂ)` on the subtype $U$. Holomorphy is expressed for the extension by zero, `extend U f` (equal to $f$ on $U$ and to $0$ off $U$), as `DifferentiableOn ℂ (extend U f) U`; for open $U$ this is ordinary holomorphy of $f$. The closure is taken in Mathlib's compact-open topology on `C(U, ℂ)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/NormalFamilies.lean#L179-L201

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

theorem OAI.DirectCrouzeix.Conformal.bounded_holomorphic_compact {U : Set ℂ} (hU : IsOpen U)
    (S : Set C(U, ℂ))
    (hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U ∧ ∀ z : U, ‖f z‖ ≤ 1) :
    IsCompact (closure S) := by sorry
