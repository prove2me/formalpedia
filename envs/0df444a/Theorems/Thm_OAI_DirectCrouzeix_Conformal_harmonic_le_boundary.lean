-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_harmonic_le_boundary
-- name    : OAI.DirectCrouzeix.Conformal.harmonic_le_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:03:32.202979+00:00
-- url     : https://prove2.me/theorems/362e50d8-6e47-4b96-949a-bdf8d1cdf59a
-- title:
--   Weak maximum principle for harmonic functions on bounded open subsets of the plane
-- statement:
--   Let $U\subseteq\mathbb{C}$ be a bounded open set and let $u:\mathbb{C}\to\mathbb{R}$ be harmonic on $U$ (as a function of the two real variables $\operatorname{Re}z,\operatorname{Im}z$) and continuous on the closure $\overline U$. If $M\in\mathbb{R}$ bounds $u$ on the boundary, that is, $u(z)\le M$ for every $z\in\partial U$, then
--
--   $$
--   u(z)\le M\qquad\text{for all } z\in\overline U .
--   $$
--
--   This is the weak maximum principle for harmonic functions in the plane; no connectedness of $U$ is required. Applied to $u-w$ and to $w-u$, it shows that two functions harmonic on a bounded open set, continuous up to the boundary and equal on the boundary, coincide on $\overline U$; in this development that uniqueness is used to identify harmonic functions with Poisson integrals.
--
--   **Formalization Note** Harmonicity is Mathlib's `HarmonicOnNhd u U`: at every point of $U$ the function is $C^2$ on a neighbourhood and its Laplacian vanishes on a neighbourhood. Together with continuity on $\overline U$ this is the predicate `HarmonicContOnCl u U`. The boundary $\partial U$ is the topological frontier `frontier U`, which equals $\overline U\setminus U$ because $U$ is open.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/PoissonBoundary.lean#L167-L197

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Function Complex
open scoped Pointwise
open InnerProductSpace Real

theorem OAI.DirectCrouzeix.Conformal.harmonic_le_boundary {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) {u : ℂ → ℝ}
    (hu : HarmonicContOnCl u U) {M : ℝ}
    (hM : ∀ z ∈ frontier U, u z ≤ M) :
    ∀ z ∈ closure U, u z ≤ M := by sorry
