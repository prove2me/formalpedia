-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_analytic_inverse_chart
-- name    : OAI.DirectCrouzeix.Geometry.analytic_inverse_chart
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:18:12.652907+00:00
-- url     : https://prove2.me/theorems/08b988ae-1c8b-406a-8dd3-044542001e1c
-- title:
--   Analytic inverse function theorem between complex Banach spaces
-- statement:
--   Let $E$ and $F$ be complex Banach spaces, let $f:E\to F$ and $x\in E$, and assume that $f$ is analytic at $x$, i.e. it is given by a convergent power series on a neighbourhood of $x$. Assume further that $f$ is Fréchet differentiable at $x$ and that its derivative there is a continuous linear isomorphism $e:E\to F$ (a bounded linear bijection with bounded inverse), $Df(x)=e$. Then there exist open sets $\Sigma\subseteq E$ and $T\subseteq F$ with $x\in\Sigma$ such that $f$ restricts to a homeomorphism of $\Sigma$ onto $T$ whose inverse $\psi:T\to\Sigma$ is analytic at $f(x)$:
--
--   $$
--   f|_{\Sigma}:\Sigma\to T\ \text{is a homeomorphism},\qquad x\in\Sigma,\qquad \psi=(f|_{\Sigma})^{-1}\ \text{is analytic at } f(x).
--   $$
--
--   This is the inverse function theorem in the analytic category: the local inverse of an analytic map with invertible derivative is again analytic at the image point, not merely continuously differentiable. It is the basic tool for building holomorphic charts and analytic implicit functions in one and several complex variables.
--
--   **Formalization Note** The conclusion is an `OpenPartialHomeomorph E F` whose underlying total function is $f$ itself (`(U : E → F) = f`), with source $\Sigma$ and target $T$. Its inverse `U.symm` is a total function from $F$ to $E$ that agrees with $\psi$ on $T$; since $T$ is an open neighbourhood of $f(x)$, analyticity of `U.symm` at $f(x)$ is analyticity of $\psi$. The derivative hypothesis is `HasFDerivAt f e x` for `e : E ≃L[ℂ] F`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/AnalyticCharts.lean#L31-L51

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

theorem OAI.DirectCrouzeix.Geometry.analytic_inverse_chart {E : Type u_133} {F : Type u_134} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {x : E} (ha : AnalyticAt ℂ f x) (e : E ≃L[ℂ] F)
    (hd : HasFDerivAt f e.toContinuousLinearMap x) :
    ∃ U : OpenPartialHomeomorph E F, (U : E → F) = f ∧ x ∈ U.source ∧
      AnalyticAt ℂ U.symm (f x) := by sorry
