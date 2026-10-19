-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_holomorphic_reflection_modulus
-- name    : OAI.DirectCrouzeix.Conformal.holomorphic_reflection_modulus
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:08:28.94528+00:00
-- url     : https://prove2.me/theorems/619050d9-8eed-4332-a596-e5aa472889f7
-- title:
--   Reflection principle for holomorphic functions whose modulus tends to $1$ on a diameter
-- statement:
--   Let $R>0$, let $B(0,R)=\{z\in\mathbb{C}:|z|<R\}$, and let
--   $$K=\{z\in\mathbb{C}:\ |z|\le R,\ \operatorname{Im}z>0\}$$
--   be the closed upper half-disk with its real diameter removed. Let $f:\mathbb{C}\to\mathbb{C}$ satisfy:
--
--   1. $f$ is holomorphic on a neighbourhood of every point of $K$;
--   2. $f(z)\neq0$ and $|f(z)|<1$ for every $z\in K$;
--   3. for every real $x$ with $|x|\le R$, $|f(w)|\to1$ as $w\to x$ through the open upper half-plane $\{w:\operatorname{Im}w>0\}$.
--
--   Then there is a function $F:\mathbb{C}\to\mathbb{C}$ with the following properties:
--
--   $$
--   \begin{aligned}
--   &F \text{ is holomorphic on } B(0,R), \qquad F(z)=f(z) \text{ for } |z|<R,\ \operatorname{Im}z>0,\\
--   &|F(z)|=1 \text{ for } |z|<R,\ \operatorname{Im}z=0, \qquad F'(0)\neq0,\\
--   &|F(z)|<1 \iff \operatorname{Im}z>0 \qquad \text{for every } z\in B(0,R).
--   \end{aligned}
--   $$
--
--   Thus $f$ continues analytically across the diameter, and the continuation maps the upper half-disk into the open unit disk, the real diameter into the unit circle and the lower half-disk into $\{w:|w|\ge1\}$, with nonzero derivative at the center. This is a reflection principle for holomorphic functions whose modulus tends to $1$ along a straight boundary segment; composed with analytic boundary charts it allows a conformal map onto the unit disk to be continued analytically across analytic arcs of the boundary of its domain.
--
--   **Formalization Note** Condition 1 is `AnalyticOnNhd ℂ f (closedBall 0 R ∩ {z | 0 < z.im})`, i.e. analyticity at every point of $K$, including the points of the arc $|z|=R$; the holomorphy of $F$ is `AnalyticOnNhd ℂ F (ball 0 R)`. The limit in condition 3 is along the neighbourhood filter of $x$ restricted to the open upper half-plane, and $F'(0)$ is `deriv F 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/HolomorphicReflection.lean#L137-L257

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

theorem OAI.DirectCrouzeix.Conformal.holomorphic_reflection_modulus {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R ∩ {z | 0 < z.im}))
    (hn : ∀ z ∈ closedBall 0 R ∩ {z | 0 < z.im}, f z ≠ 0)
    (hb : ∀ z ∈ closedBall 0 R ∩ {z | 0 < z.im}, ‖f z‖ < 1)
    (hl : ∀ z ∈ closedBall 0 R, z.im = 0 →
      Tendsto (fun w => ‖f w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 1)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball 0 R) ∧ EqOn F f (upperBall R) ∧
      (∀ z ∈ ball 0 R, z.im = 0 → ‖F z‖ = 1) ∧ deriv F 0 ≠ 0 ∧
      (∀ z ∈ ball 0 R, ‖F z‖ < 1 ↔ 0 < z.im) := by sorry
