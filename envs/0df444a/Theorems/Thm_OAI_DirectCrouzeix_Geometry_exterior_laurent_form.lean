-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_exterior_laurent_form
-- name    : OAI.DirectCrouzeix.Geometry.exterior_laurent_form
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:33:12.765982+00:00
-- url     : https://prove2.me/theorems/257c2958-fadc-4920-9e6b-404fae6c89a1
-- title:
--   Inverting a univalent disk map gives an exterior map in Laurent form $c\zeta+g(1/\zeta)$
-- statement:
--   Let $R>0$ and write $D_R=\{u\in\mathbb{C}:\ |u|<R\}$. Let $f:\mathbb{C}\to\mathbb{C}$ be complex-analytic at every point of $D_R$ and injective on $D_R$, with
--
--   $$
--   f(0)=0\qquad\text{and}\qquad f'(u)\neq0\ \text{ for all }u\in D_R ,
--   $$
--
--   and let $a\in\mathbb{C}$ be arbitrary.
--
--   **Theorem.** There exist a constant $c\in\mathbb{C}$ with $c\neq0$ and a function $g:\mathbb{C}\to\mathbb{C}$, complex-analytic at every point of $D_R$, such that the function
--
--   $$
--   \Phi(\zeta)=c\,\zeta+g\bigl(1/\zeta\bigr)\qquad(\zeta\neq0)
--   $$
--
--   has the following properties.
--
--   1. For every $\zeta\neq0$: $\ \Phi(\zeta)=a+\dfrac{1}{f(1/\zeta)}$.
--   2. $\Phi$ is injective on the exterior region $\{\zeta\in\mathbb{C}:\ |\zeta|>1/R\}$.
--   3. $\Phi'(\zeta)\neq0$ for every $\zeta$ with $|\zeta|>1/R$.
--
--   For $|\zeta|>1/R$ the point $1/\zeta$ is a nonzero point of $D_R$, so $f(1/\zeta)\neq f(0)=0$ and the right-hand side of item 1 is an honest quotient.
--
--   Composing a univalent map of a disk with the inversion $w\mapsto a+1/w$ produces a univalent map of a neighbourhood of infinity with a simple pole there. The theorem puts it into the normal form $c\zeta+g(1/\zeta)$, that is, a Laurent series $c\zeta+g_0+g_1\zeta^{-1}+g_2\zeta^{-2}+\cdots$ converging for $|\zeta|>1/R$ with nonzero leading coefficient. This is the form in which exterior conformal maps enter the construction of Faber polynomials.
--
--   **Formalization Note** Analyticity on the disk is `AnalyticOnNhd ℂ g (ball 0 R)`, the exterior region is written `Inv.inv ⁻¹' ball 0 R \ {0}` (the nonzero $\zeta$ with $1/\zeta\in D_R$), and $\Phi'$ is `deriv` of the map $\zeta\mapsto c\zeta+g(1/\zeta)$. Item 1 is asserted for every nonzero $\zeta$ and uses Lean's field inverse, for which the inverse of $0$ is $0$. For $0<|\zeta|\le1/R$ the hypotheses say nothing about $f(1/\zeta)$, and the identity there is a property of the particular $g$ constructed, read with this convention if $f(1/\zeta)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/ExteriorMapping.lean#L49-L109

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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExponentialLevels
import Definitions.Def_OAI_Analysis_DirectCrouzeix_InverseExterior

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Geometry
universe u_138 u_139
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate

theorem OAI.DirectCrouzeix.Geometry.exterior_laurent_form {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hinj : InjOn f (ball 0 R))
    (hf0 : f 0 = 0) (hd : ∀ u ∈ ball 0 R, deriv f u ≠ 0) (a : ℂ) :
    ∃ (c : ℂ) (g : ℂ → ℂ), c ≠ 0 ∧ AnalyticOnNhd ℂ g (ball 0 R) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → c*ζ+g ζ⁻¹ = a+(f ζ⁻¹)⁻¹) ∧
      InjOn (fun ζ => c*ζ+g ζ⁻¹) (Inv.inv ⁻¹' ball 0 R \ {0}) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → ζ⁻¹ ∈ ball 0 R → deriv (fun ζ => c*ζ+g ζ⁻¹) ζ ≠ 0) := by sorry
