-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_hasDerivAt_sphereAverage_center
-- name    : HunterPDE.Harmonic.hasDerivAt_sphereAverage_center
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T14:56:48.595092+00:00
-- url     : https://prove2.me/theorems/519e43d0-d68a-4b9a-b812-92c0a82d6d2c
-- title:
--   Differentiation of spherical averages with respect to their centre
-- statement:
--   Let $n\ge1$, $r>0$, $x,v\in\mathbb R^n$, and let $u:\mathbb R^n\to\mathbb R$ be continuously differentiable near each point of $\overline B_r(x)$. With $A_u(z,r)$ denoting the normalized spherical average,
--
--   $$\left.\frac{d}{dt}A_u(x+tv,r)\right|_{t=0}=\fint_{S^{n-1}}Du(x+r\omega)[v]\,d\sigma(\omega).$$
--
--   This identity differentiates on a fixed unit sphere and is useful when translating averaging identities into identities for derivatives.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed p. 23, proof of Theorem 2.7; mean-value identities: printed p. 20, Theorem 2.1; polar integration: printed p. 17, Proposition 1.45.

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp

open MeasureTheory Set Filter Topology
open HunterPDE.Harmonic

theorem HunterPDE.Harmonic.hasDerivAt_sphereAverage_center {n : ℕ} (hn : 0 < n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r)
    (hu : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 1 u y)
    (v : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun t : ℝ => sphereAverage u (x + t • v) r)
      (⨍ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        fderiv ℝ u (x + r • ω.1) v ∂(volume.toSphere)) 0 := by sorry
