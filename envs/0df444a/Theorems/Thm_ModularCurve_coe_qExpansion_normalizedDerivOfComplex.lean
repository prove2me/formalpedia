-- Prove2me | Theorems.Thm_ModularCurve_coe_qExpansion_normalizedDerivOfComplex
-- name    : ModularCurve.coe_qExpansion_normalizedDerivOfComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/81d39c60-3004-5e5a-9072-36998eb4606e
-- title:
--   q-expansion of the normalised derivative equals θ of the q-expansion
-- statement:
--   Let $F \colon \mathbb{H} \to \mathbb{C}$ be a function on the upper half plane such that the composite $F \circ$ `UpperHalfPlane.ofComplex` is periodic of period $1$, such that $F$ is differentiable as a map of complex manifolds (with the standard charts on source and target), and such that $F$ is bounded at $i\infty$ in the sense of `UpperHalfPlane.IsBoundedAtImInfty`. Form the $q$-expansion of period $1$ of the function `Derivative.normalizedDerivOfComplex F` obtained from $F$, and the $q$-expansion of period $1$ of $F$ itself; both are power series over $\mathbb{C}$, and each is regarded as a Laurent series via the canonical inclusion of `PowerSeries ℂ` into `LaurentSeries ℂ`. The assertion is the equality of Laurent series
--   $$\mathrm{qExp}\bigl(\mathrm{normalizedDerivOfComplex}\,F\bigr) = \theta\bigl(\mathrm{qExp}(F)\bigr),$$
--   where $\theta =$ [`ModularCurve.thetaL ℂ`](def/ModularCurve_QExpansionDiff.html#L16) is the $\mathbb{C}$-linear operator on `LaurentSeries ℂ` sending $f$ to $\mathrm{single}(1,1) \cdot \mathrm{derivative}(f)$, that is, the operator $q\,\mathrm{d}/\mathrm{d}q$, whose effect on coefficients is multiplication of the coefficient of $q^{n}$ by $n$. No modularity or weight hypothesis on $F$ occurs; the conclusion is an identity of formal series.
--
--   This packages the coefficientwise description of the normalised derivative $\tfrac{1}{2\pi i}\,\mathrm{d}/\mathrm{d}\tau$ on $q$-expansions as a single identity between a transcendentally defined operator on functions on $\mathbb{H}$ and the purely formal operator $q\,\mathrm{d}/\mathrm{d}q$ on Laurent series, the coefficient computation being supplied by [`ModularCurve.theta_coeff`](thm.html#ModularCurve.theta_coeff). It is used in the computation of the $q$-expansion of the first Rankin–Cohen bracket, [`ModularForm.exists_rankinCohen_one_qExpansion_eq`](thm.html#ModularForm.exists_rankinCohen_one_qExpansion_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coe_qExpansion_normalizedDerivOfComplex.lean

import Definitions.Def_ModularCurve_QExpansionDiff
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane Complex Function ModularCurve
open scoped Real Manifold

theorem ModularCurve.coe_qExpansion_normalizedDerivOfComplex (F : ℍ → ℂ) (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) :
    ((UpperHalfPlane.qExpansion 1 (Derivative.normalizedDerivOfComplex F) : PowerSeries ℂ) :
        LaurentSeries ℂ) =
      ModularCurve.thetaL ℂ
        ((UpperHalfPlane.qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ) := by sorry
