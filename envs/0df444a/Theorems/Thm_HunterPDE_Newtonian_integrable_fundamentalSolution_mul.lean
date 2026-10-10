-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_integrable_fundamentalSolution_mul
-- name    : HunterPDE.Newtonian.integrable_fundamentalSolution_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T20:44:11.574036+00:00
-- url     : https://prove2.me/theorems/960af785-6545-4c1b-9430-70a861427c63
-- title:
--   Integrability of Newtonian potentials of continuous compactly supported data
-- statement:
--   Let $n\ge2$, and let $\Gamma_n$ be Hunter's fundamental solution of $-\Delta$ on $\mathbb R^n$. For every continuous compactly supported real function $g$ and every $x\in\mathbb R^n$,
--
--   $$y\longmapsto\Gamma_n(x-y)g(y)\quad\hbox{belongs to }L^1(\mathbb R^n).$$
--
--   This supplies genuine Lebesgue integrals for Newtonian potentials without requiring differentiability of the source. The value assigned to the kernel at its singular point does not affect integrability.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 33–36: Eq. (2.12), local integrability in §2.6.1, Eq. (2.19)–(2.23); Green identity Eq. (2.11), printed p. 32. The ball-integral form of the boundary flux uses the divergence theorem, Theorem 1.46, printed p. 17.

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.InnerProductSpace.Laplacian

open MeasureTheory Filter Set Topology
open scoped ContDiff
open Laplacian
open HunterPDE.Newtonian HunterPDE.Harmonic

theorem HunterPDE.Newtonian.integrable_fundamentalSolution_mul (n : ℕ) (hn : 2 ≤ n)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => fundamentalSolution n (x - y) * g y) := by sorry
