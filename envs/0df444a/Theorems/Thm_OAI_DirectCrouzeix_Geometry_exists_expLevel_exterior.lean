-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_exists_expLevel_exterior
-- name    : OAI.DirectCrouzeix.Geometry.exists_expLevel_exterior
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:35:27.468053+00:00
-- url     : https://prove2.me/theorems/92624be6-f730-40c3-96ff-65cbc6170027
-- title:
--   Univalent exterior map $c\zeta+g(1/\zeta)$ sending the unit circle into the level curve of an exponential sum
-- statement:
--   Let $\iota$ be a finite index set, let $v_i\in\mathbb{C}$ and $b_i\in\mathbb{R}$ for $i\in\iota$, equip $\mathbb{C}$ with the real inner product $\langle w,z\rangle=\operatorname{Re}(\overline{w}\,z)$, and let
--
--   $$
--   E(z)=\sum_{i\in\iota}\exp\bigl(\langle v_i,z\rangle+b_i\bigr),\qquad z\in\mathbb{C}.
--   $$
--
--   Assume that the sublevel set $\{z\in\mathbb{C}:\ E(z)\le1\}$ is compact and that some point $a\in\mathbb{C}$ satisfies $E(a)<1$.
--
--   **Theorem.** There exist a radius $R>1$, a constant $c\in\mathbb{C}$ with $c\neq0$, and a function $g:\mathbb{C}\to\mathbb{C}$ that is complex-analytic at every point of the disk $D_R=\{u:\ |u|<R\}$, such that the function
--
--   $$
--   \Phi(\zeta)=c\,\zeta+g\bigl(1/\zeta\bigr)
--   $$
--
--   satisfies:
--
--   1. $\Phi$ is injective on $\{\zeta\in\mathbb{C}:\ |\zeta|>1/R\}$;
--   2. $\Phi'(\zeta)\neq0$ for every $\zeta$ with $|\zeta|>1/R$;
--   3. $E(\Phi(\zeta))=1$ for every $\zeta$ with $|\zeta|=1$;
--   4. $E(\Phi(\zeta))>1$ for every $\zeta$ with $|\zeta|>1$.
--
--   Since $1/R<1$, the map $\Phi$ is univalent and locally biholomorphic on a neighbourhood of the closed exterior $\{|\zeta|\ge1\}$ of the unit disk, has a simple pole at infinity, maps the unit circle into the level curve $\{E=1\}$, and maps $\{|\zeta|>1\}$ into the region $\{E>1\}$ outside the compact convex set $\{E\le1\}$. It thus provides, for these smooth convex sets, an exterior map in Laurent normal form that continues analytically across the unit circle, so that the boundary curve $\theta\mapsto\Phi(e^{i\theta})$ is real-analytic. Sublevel sets $\{E\le1\}$ of this kind serve as smooth outer approximations of compact convex sets such as numerical ranges.
--
--   **Formalization Note** The exponential sum is `expLevel v b`; $g$ is analytic in the sense `AnalyticOnNhd ℂ g (ball 0 R)`; the domain of injectivity is written `Inv.inv ⁻¹' ball 0 R \ {0}` and the derivative condition is stated for nonzero $\zeta$ with $1/\zeta\in D_R$, both of which describe the region $|\zeta|>1/R$. The theorem does not assert that $\Phi$ maps onto the exterior of $\{E\le1\}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/ExteriorMapping.lean#L148-L197

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

theorem OAI.DirectCrouzeix.Geometry.exists_expLevel_exterior {ι : Type u_139} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | expLevel v b z ≤ 1})
    {a : ℂ} (ha : expLevel v b a < 1) :
    ∃ R > 1, ∃ (c : ℂ) (g : ℂ → ℂ), c ≠ 0 ∧ AnalyticOnNhd ℂ g (ball 0 R) ∧
      InjOn (fun ζ => c*ζ+g ζ⁻¹) (Inv.inv ⁻¹' ball 0 R \ {0}) ∧
      (∀ ζ : ℂ, ζ ≠ 0 → ζ⁻¹ ∈ ball 0 R → deriv (fun ζ => c*ζ+g ζ⁻¹) ζ ≠ 0) ∧
      (∀ ζ : ℂ, ‖ζ‖ = 1 → expLevel v b (c*ζ+g ζ⁻¹) = 1) ∧
      (∀ ζ : ℂ, 1 < ‖ζ‖ → 1 < expLevel v b (c*ζ+g ζ⁻¹)) := by sorry
