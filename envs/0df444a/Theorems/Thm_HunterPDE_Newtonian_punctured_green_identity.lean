-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_punctured_green_identity
-- name    : HunterPDE.Newtonian.punctured_green_identity
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T20:45:55.083338+00:00
-- url     : https://prove2.me/theorems/7e4e22c9-09e9-4ce6-a296-9152df83b883
-- title:
--   Green representation outside a ball for compactly supported C² functions
-- statement:
--   Let $n\ge2$, $f\in C_c^2(\mathbb R^n)$, $x\in\mathbb R^n$, $r>0$, and let $v$ be any unit vector. Write $A_f(x,r)$ for the normalized surface average of $f$ on $\partial B_r(x)$. Then
--
--   $$\int_{\mathbb R^n\setminus B_r(x)}\Gamma_n(x-y)\Delta f(y)\,dy
--   =-\Gamma_n(rv)\int_{B_r(x)}\Delta f(y)\,dy-A_f(x,r).$$
--
--   This is the finite-radius Green representation in Hunter's Eq. (2.20), with the outward derivative flux of $f$ expressed as a ball integral of its Laplacian. The kernel is radial, so the choice of unit vector has no effect. This formula isolates the integration-by-parts argument before the singular radius tends to zero.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 33–36: Eq. (2.12), local integrability in §2.6.1, Eq. (2.19)–(2.23); Green identity Eq. (2.11), printed p. 32. The ball-integral form of the boundary flux uses the divergence theorem, Theorem 1.46, printed p. 17.

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.InnerProductSpace.Laplacian

open MeasureTheory Filter Set Topology
open scoped ContDiff
open Laplacian
open HunterPDE.Newtonian HunterPDE.Harmonic

theorem HunterPDE.Newtonian.punctured_green_identity (n : ℕ) (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) (r : ℝ) (hr : 0 < r) :
    (∫ y in (Metric.ball x r)ᶜ, fundamentalSolution n (x - y) * (Δ f) y) =
      -fundamentalSolution n (r • v) * (∫ y in Metric.ball x r, (Δ f) y) -
        sphereAverage f x r := by sorry
