-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_local_riemann_extension
-- name    : OAI.DirectCrouzeix.Conformal.local_riemann_extension
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:16:14.969981+00:00
-- url     : https://prove2.me/theorems/d9af7440-91a4-495b-966f-bdae93b7ef84
-- title:
--   Analytic continuation of a Riemann map across a boundary point with an analytic half-plane chart
-- statement:
--   Let $U\subseteq\mathbb{C}$ be open, let $a\in U$, and let $\mathbb{D}=\{w\in\mathbb{C}:|w|<1\}$ be the open unit disk. Let $f:\mathbb{C}\to\mathbb{C}$ be a *normalized embedding of $U$ at $a$*: $f$ is holomorphic on $U$, maps $U$ into $\mathbb{D}$, is injective on $U$, satisfies $f'(z)\neq0$ for all $z\in U$, and $f(a)=0$. Assume moreover that $f(U)=\mathbb{D}$, so that $f$ is a conformal bijection of $U$ onto the disk sending $a$ to $0$.
--
--   Let $p\in\mathbb{C}\setminus U$, and let $\varphi$ be an *analytic boundary chart of $U$ at $p$*: open sets $\Sigma,T\subseteq\mathbb{C}$ and a homeomorphism $\varphi:\Sigma\to T$ with inverse $\psi:T\to\Sigma$ such that $0\in\Sigma$, $\varphi(0)=p$, $\varphi$ is analytic at every point of $\Sigma$, $\psi$ is analytic at every point of $T$, $\psi'(p)\neq0$, and $\varphi(z)\in U\iff\operatorname{Im}z>0$ for every $z\in\Sigma$. Write $D(p,\rho)=\{z\in\mathbb{C}:|z-p|<\rho\}$. Then there exist $r>0$ and a function $E:\mathbb{C}\to\mathbb{C}$, analytic at every point of $D(p,3r)$, such that
--
--   $$
--   E=f\ \text{ on } D(p,3r)\cap U,\qquad |E(z)|<1\iff z\in U\quad\text{for } z\in D(p,3r),\qquad E'(p)\neq0 .
--   $$
--
--   In words: at a boundary point near which $U$ is, in analytic coordinates, the upper half-plane, the Riemann map $f$ continues analytically across the boundary with nonvanishing derivative, and the continuation has modulus less than $1$ exactly on $U$. These are precisely the local hypotheses of the lemma that glues such local continuations into an analytic continuation of $f$ on a neighbourhood of $\overline{U}$; the radius is written as $3r$ to match it.
--
--   **Formalization Note** The normalized embedding is the structure `NormalizedEmbedding U a f`, with holomorphy stated as `DifferentiableOn ℂ f U`. The chart is a term `C : AnalyticBoundaryChart U p`, whose field `chart` is an `OpenPartialHomeomorph ℂ ℂ` with source $\Sigma$, target $T$ and total inverse function `chart.symm`; analyticity on a set is `AnalyticOnNhd ℂ` and derivatives are Lean's `deriv`. The hypothesis $p\notin U$ is in fact implied by the chart (take $z=0$ in its side condition).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/ConformalCollar.lean#L43-L127

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Function Complex
open scoped Pointwise
open InnerProductSpace Real

theorem OAI.DirectCrouzeix.Conformal.local_riemann_extension {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) {p : ℂ} (hp : p ∉ U)
    (C : AnalyticBoundaryChart U p) :
    ∃ r > 0, ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (ball p (3*r)) ∧
      EqOn E f (ball p (3*r) ∩ U) ∧
      (∀ z ∈ ball p (3*r), ‖E z‖ < 1 ↔ z ∈ U) ∧ deriv E p ≠ 0 := by sorry
