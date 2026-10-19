-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_analytic_complex_chart
-- name    : OAI.DirectCrouzeix.Geometry.analytic_complex_chart
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:22:41.249455+00:00
-- url     : https://prove2.me/theorems/8ef3ff8a-6706-4d6b-b32f-f3c95653d1cc
-- title:
--   Holomorphic chart with analytic inverse inside any prescribed neighbourhood of the base point
-- statement:
--   Let $f:\mathbb{C}\to\mathbb{C}$ be analytic at $0$ with $f'(0)\neq0$, and let $P$ be a property of complex numbers that holds at every point of some neighbourhood of $0$. Then there are open sets $\Sigma,T\subseteq\mathbb{C}$ with $0\in\Sigma$ such that $f$ restricts to a homeomorphism of $\Sigma$ onto $T$, with inverse $\psi:T\to\Sigma$, and
--
--   $$
--   f\ \text{is analytic at every point of }\Sigma,\qquad \psi\ \text{is analytic at every point of }T,\qquad \psi'(f(0))\neq0,\qquad P(z)\ \text{holds for all } z\in\Sigma .
--   $$
--
--   This is the holomorphic inverse function theorem in the form used to produce charts: the chart is analytic in both directions on its whole domain, not only at the base point, and its domain can be placed inside any given neighbourhood of $0$, for instance one on which a desired side condition holds. In the surrounding development it supplies the analytic boundary charts of domains bounded by level curves.
--
--   **Formalization Note** The conclusion is an `OpenPartialHomeomorph ℂ ℂ` whose underlying total function is $f$ itself, with source $\Sigma$, target $T$, and total inverse function `U.symm` agreeing with $\psi$ on $T$. Analyticity on a set is `AnalyticOnNhd ℂ`, the property is a predicate `P : ℂ → Prop` with `∀ᶠ z in 𝓝 0, P z`, and $\psi'(f(0))$ is Lean's `deriv` of `U.symm` at `f 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/AnalyticCharts.lean#L187-L223

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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ConformalCollar
import Definitions.Def_OAI_Analysis_DirectCrouzeix_AnalyticCharts

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Geometry
universe u_133 u_134 u_135
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate

theorem OAI.DirectCrouzeix.Geometry.analytic_complex_chart {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hd : deriv f 0 ≠ 0) {P : ℂ → Prop} (hP : ∀ᶠ z in 𝓝 0, P z) :
    ∃ U : OpenPartialHomeomorph ℂ ℂ, (U : ℂ → ℂ) = f ∧ 0 ∈ U.source ∧
      AnalyticOnNhd ℂ U U.source ∧ AnalyticOnNhd ℂ U.symm U.target ∧
      deriv U.symm (f 0) ≠ 0 ∧ (∀ z ∈ U.source, P z) := by sorry
