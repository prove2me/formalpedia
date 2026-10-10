-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_secondPartial_newtonianPotential_boundary_ball
-- name    : HunterPDE.Newtonian.secondPartial_newtonianPotential_boundary_ball
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-09T22:59:33.578697+00:00
-- url     : https://prove2.me/theorems/35a07359-14bc-4af0-8f6f-e85f6612f934
-- title:
--   Newtonian Hessian representation with the unevaluated spherical boundary flux
-- statement:
--   Let $n\ge2$, $f\in C_c^\infty(\mathbb R^n)$, and $u=\Gamma*f$. If $R>0$ and the closed support of $f$ is contained in $B_R(x)$, then
--
--   $$\partial_{ij}u(x)=\int_{B_R(x)}\partial_{ij}\Gamma(x-y)(f(y)-f(x))\,dy-f(x)R^{n-1}\int_{S^{n-1}}\partial_i\Gamma(-R\omega)\omega_j\,dS(\omega).$$
--
--   The last integral is the unevaluated outward boundary flux, parametrized by $y=x+R\omega$. This is Hunter Theorem 2.26, Eq. (2.25), specialized to a ball. Its proof differentiates on the smooth source, integrates by parts outside a small ball, subtracts $f(x)$, and lets the excluded radius tend to zero as in Eqs. (2.26)–(2.28). Evaluation of the spherical coefficient is a separate obligation.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, pp. 37–39, Theorem 2.26 Eqs. (2.25)–(2.28), Corollary 2.27 Eq. (2.29).

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_HunterPDE_Newtonian_NewtonianPotential
import Mathlib.MeasureTheory.Constructions.HaarToSphere
open MeasureTheory HunterPDE.Newtonian
open scoped ContDiff

theorem HunterPDE.Newtonian.secondPartial_newtonianPotential_boundary_ball
    (n : ℕ) (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R)
    (hsupp : tsupport f ⊆ Metric.ball x R) (i j : Fin n) :
    secondPartial (newtonianPotential n f) i j x =
      (∫ y in Metric.ball x R, secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x))
        - f x * (R ^ (n - 1) *
          (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
            partialDeriv (fundamentalSolution n) i (-(R • w.1)) * w.1 j ∂volume.toSphere)) := by sorry
