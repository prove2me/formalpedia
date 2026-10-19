-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_exists_extremalEmbedding
-- name    : OAI.DirectCrouzeix.Conformal.exists_extremalEmbedding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:00:01.912079+00:00
-- url     : https://prove2.me/theorems/df5b96b8-1681-45db-9df7-49668c789615
-- title:
--   Existence of an extremal normalized embedding of a simply connected domain into the unit disk
-- statement:
--   Let $U\subseteq\mathbb{C}$ be an open, simply connected set with $U\neq\mathbb{C}$, let $a\in U$, and write $\mathbb{D}=\{w\in\mathbb{C}:|w|<1\}$ for the open unit disk. A function $f:\mathbb{C}\to\mathbb{C}$ is called a *normalized embedding of $U$ at $a$* if
--
--   1. $f$ is holomorphic on $U$;
--   2. $f(U)\subseteq\mathbb{D}$;
--   3. $f$ is injective on $U$;
--   4. $f'(z)\neq0$ for every $z\in U$;
--   5. $f(a)=0$.
--
--   Only the values of $f$ on $U$ matter. The theorem asserts that there is a normalized embedding $f$ of $U$ at $a$ whose derivative at $a$ has the largest possible modulus:
--
--   $$
--   |g'(a)|\le|f'(a)|\qquad\text{for every normalized embedding } g \text{ of } U \text{ at } a .
--   $$
--
--   This is the extremal problem behind the classical proof of the Riemann mapping theorem. Combined with the fact that a normalized embedding whose image omits a point of $\mathbb{D}$ can be replaced by one with strictly larger $|f'(a)|$, it shows that an extremal embedding maps $U$ onto $\mathbb{D}$, which is how a Riemann map of $U$ is obtained in this development.
--
--   **Formalization Note** Functions are total maps $\mathbb{C}\to\mathbb{C}$. Holomorphy on $U$ is `DifferentiableOn ℂ f U` (equivalent to holomorphy because $U$ is open), $f'$ is Lean's complex derivative `deriv f`, and simple connectivity is Mathlib's `IsSimplyConnected` (path-connected, with every loop null-homotopic). The five conditions form the structure `NormalizedEmbedding U a f`; condition 4 is included in the definition although it also follows from injectivity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/ExtremalEmbedding.lean#L164-L233

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

theorem OAI.DirectCrouzeix.Conformal.exists_extremalEmbedding {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedEmbedding U a f ∧
      ∀ g, NormalizedEmbedding U a g → ‖deriv g a‖ ≤ ‖deriv f a‖ := by sorry
