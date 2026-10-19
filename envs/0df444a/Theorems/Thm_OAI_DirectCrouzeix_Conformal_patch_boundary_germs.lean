-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_patch_boundary_germs
-- name    : OAI.DirectCrouzeix.Conformal.patch_boundary_germs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:12:21.050494+00:00
-- url     : https://prove2.me/theorems/ff8603b3-456a-4611-9fe8-7c3baf4f1ee4
-- title:
--   Gluing local analytic extensions with the unit-disk side property into one extension near $\overline{U}$
-- statement:
--   Let $U\subseteq\mathbb{C}$ be an open set with closure $\overline{U}$, let $f:\mathbb{C}\to\mathbb{C}$ be an arbitrary function, and write $D(p,\rho)=\{z\in\mathbb{C}:|z-p|<\rho\}$ for the open disk of radius $\rho$ about $p$. Assume that for every $p\in\overline{U}$ there are a radius $r_p>0$ and a function $E_p:\mathbb{C}\to\mathbb{C}$ such that
--
--   1. $E_p$ is analytic at every point of $D(p,3r_p)$;
--   2. $E_p(z)=f(z)$ for all $z\in D(p,3r_p)\cap U$;
--   3. for every $z\in D(p,3r_p)$, one has $|E_p(z)|<1$ if and only if $z\in U$;
--   4. $E_p'(p)\neq0$.
--
--   Then there are an open set $V\subseteq\mathbb{C}$ and a function $F:\mathbb{C}\to\mathbb{C}$ such that $\overline{U}\subseteq V$, $F$ is analytic at every point of $V$, $F(z)=f(z)$ for all $z\in U$, and
--
--   $$
--   |F(z)|<1\iff z\in U\quad\text{for all } z\in V,\qquad\qquad F'(p)\neq0\quad\text{for all } p\in\overline{U}.
--   $$
--
--   In words: local analytic extensions of $f$ across the boundary of $U$, each of which has modulus less than $1$ exactly on $U$, can be glued into a single analytic extension on a neighbourhood of $\overline{U}$ with the same two properties. No compatibility between the extensions at different points is assumed. This is the gluing step in continuing a conformal map of a domain with analytic boundary onto the unit disk analytically across the whole boundary: the local extensions come from the map itself at interior points and from a reflection argument at boundary points.
--
--   **Formalization Note** Analyticity on a set is `AnalyticOnNhd ℂ`, i.e. analyticity at each point of the set, and $E_p'(p)$, $F'(p)$ are Lean's `deriv`, which is the genuine complex derivative here because the functions are analytic at $p$. Nothing is asserted about the values of $F$ outside $V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/Continuation.lean#L66-L111

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

theorem OAI.DirectCrouzeix.Conformal.patch_boundary_germs {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hloc : ∀ p ∈ closure U, ∃ r > 0, ∃ E : ℂ → ℂ,
      AnalyticOnNhd ℂ E (ball p (3*r)) ∧ EqOn E f (ball p (3*r) ∩ U) ∧
      (∀ z ∈ ball p (3*r), ‖E z‖ < 1 ↔ z ∈ U) ∧ deriv E p ≠ 0) :
    ∃ V : Set ℂ, ∃ F : ℂ → ℂ, IsOpen V ∧ closure U ⊆ V ∧
      AnalyticOnNhd ℂ F V ∧ EqOn F f U ∧
      (∀ z ∈ V, ‖F z‖ < 1 ↔ z ∈ U) ∧ (∀ p ∈ closure U, deriv F p ≠ 0) := by sorry
