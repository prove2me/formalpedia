-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_improve_embedding
-- name    : OAI.DirectCrouzeix.Conformal.improve_embedding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:00:34.051256+00:00
-- url     : https://prove2.me/theorems/b241360d-e734-4e85-b884-ea4cc1cdcb82
-- title:
--   A normalized disk embedding that omits a point of the disk can be strictly improved
-- statement:
--   Let $U\subseteq\mathbb{C}$ be an open, simply connected set, let $a\in U$, and let $\mathbb{D}=\{w\in\mathbb{C}:|w|<1\}$ be the open unit disk. Let $f:\mathbb{C}\to\mathbb{C}$ be a normalized embedding of $U$ at $a$, that is: $f$ is holomorphic and injective on $U$, $f(U)\subseteq\mathbb{D}$, $f'(z)\neq0$ for every $z\in U$, and $f(a)=0$. Suppose that $f$ misses a point of the disk: there is $b\in\mathbb{C}$ with $|b|<1$ and $b\notin f(U)$. Then there exists a normalized embedding $G$ of $U$ at $a$ with strictly larger derivative at $a$:
--
--   $$
--   |f'(a)|<|G'(a)| .
--   $$
--
--   Together with the existence (for $U\neq\mathbb{C}$) of a normalized embedding maximizing $|f'(a)|$, this shows that a maximizing embedding maps $U$ onto $\mathbb{D}$; this is how the Riemann mapping theorem is obtained in this development.
--
--   **Formalization Note** Functions are total maps $\mathbb{C}\to\mathbb{C}$ and only their values on $U$ matter. The conditions on $f$ and $G$ form the structure `NormalizedEmbedding U a f`, with holomorphy expressed as `DifferentiableOn ℂ f U` and derivatives given by `deriv`; simple connectivity is Mathlib's `IsSimplyConnected`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/DiskMapping.lean#L130-L217

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

theorem OAI.DirectCrouzeix.Conformal.improve_embedding {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U)
    {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    {b : ℂ} (hb : ‖b‖ < 1) (hmiss : b ∉ f '' U) :
    ∃ G, NormalizedEmbedding U a G ∧ ‖deriv f a‖ < ‖deriv G a‖ := by sorry
