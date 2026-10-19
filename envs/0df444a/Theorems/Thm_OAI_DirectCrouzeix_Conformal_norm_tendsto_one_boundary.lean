-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_norm_tendsto_one_boundary
-- name    : OAI.DirectCrouzeix.Conformal.norm_tendsto_one_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:01:51.33226+00:00
-- url     : https://prove2.me/theorems/bced5075-2e6a-4649-b74e-fa469e77b90d
-- title:
--   A conformal map onto the unit disk has modulus tending to $1$ at points outside its domain
-- statement:
--   Let $U\subseteq\mathbb{C}$ be open, let $a\in\mathbb{C}$, and let $\mathbb{D}=\{w\in\mathbb{C}:|w|<1\}$. Let $f:\mathbb{C}\to\mathbb{C}$ be a normalized embedding of $U$ at $a$: $f$ is holomorphic and injective on $U$, $f(U)\subseteq\mathbb{D}$, $f'(z)\neq0$ for every $z\in U$, and $f(a)=0$. Assume moreover that $f$ maps $U$ onto the disk, $f(U)=\mathbb{D}$. Then for every point $p\in\mathbb{C}\setminus U$,
--
--   $$
--   \lim_{\substack{z\to p\\ z\in U}}|f(z)|=1 .
--   $$
--
--   In words, a conformal map of $U$ onto the unit disk sends points approaching the boundary of $U$ towards the unit circle. This boundary behaviour is the input for continuing such a map analytically across analytic arcs of $\partial U$ by reflection.
--
--   **Formalization Note** The limit is taken along the filter `𝓝[U] p` of neighbourhoods of $p$ intersected with $U$; when $p$ is not in the closure of $U$ this filter is trivial and the statement holds vacuously, so the substantive case is $p\in\partial U$. The point $a$ is not required to lie in $U$, and neither simple connectivity of $U$ nor $U\neq\mathbb{C}$ is assumed. The conditions on $f$ form the structure `NormalizedEmbedding U a f`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/DiskMapping.lean#L257-L275

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Function Complex
open scoped Pointwise

theorem OAI.DirectCrouzeix.Conformal.norm_tendsto_one_boundary {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) {p : ℂ} (hp : p ∉ U) :
    Tendsto (fun z => ‖f z‖) (𝓝[U] p) (𝓝 1) := by sorry
