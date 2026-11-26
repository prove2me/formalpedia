-- Prove2me | Theorems.Thm_LefebvreVariations_laplace_rlDeriv_half_exp
-- name    : LefebvreVariations.laplace_rlDeriv_half_exp
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:33:44.790738+00:00
-- url     : https://prove2.me/theorems/40c35c18-18f4-4d5b-91fe-ea7215a5c3b2
-- title:
--   Lefebvre's variations, No. 216 — on a theme by Riemann and Liouville: the Laplace transform of the half-order Riemann-Liouville derivative of a decaying exponential
-- statement:
--   For every complex $s$ with $\operatorname{Re}s>0$, the Laplace transform of the Riemann--Liouville derivative of order $\tfrac12$ of $f(t)=e^{-t}$ is
--   $$
--   \mathcal L\bigl[D^{1/2}e^{-t}\bigr](s)\;=\;\frac{s^{1/2}}{s+1},
--   $$
--   with the principal branch of the power. Here $D^{1/2}f=\frac{d}{dt}I^{1/2}f$ with $I^{1/2}g(t)=\frac1{\Gamma(1/2)}\int_0^t(t-\tau)^{-1/2}g(\tau)\,d\tau$, and the value agrees with the general rule $s^{\nu}F(s)-\sum_{k<n}s^{n-k-1}\bigl(\tfrac{d}{dt}\bigr)^kI^{n-\nu}f(0^+)=s^{1/2}\cdot\frac1{s+1}-0$ for $\nu=\tfrac12$, $n=1$, since $I^{1/2}e^{-t}\to0$ as $t\to0^+$.
--
--   **Formalization Note** The left side is `laplace (FractionalCalc.rlDeriv 0 (1/2) (fun t => Real.exp (-t))) s`; by definition `rlDeriv 0 (1/2) f = iteratedDeriv 1 (rlIntegral 0 (1/2) f)` (here `n = ⌊1/2⌋ + 1 = 1`). `laplace` integrates over `(0, ∞)` only, and `s ^ (1/2 : ℂ)` is the principal complex power.
--
--   **Why this is a variation.** This varies the open platform problem `FractionalCalc.laplace_rlDeriv`, the Laplace transform of the Riemann--Liouville derivative of order $\nu$. Note that the parent is ill-posed as formalised (its derivatives are Mathlib's `iteratedDeriv`, which takes the junk value $0$ at points of non-differentiability, so the general formula can fail for functions with kinks); this variation avoids that: for $f=e^{-t}$ the fractional integral $I^{1/2}f$ is smooth on $(0,\infty)$, so the derivative is the genuine one. It is the explicit case $\nu=\tfrac12$, $f(t)=e^{-t}$, where the single initial value $I^{1/2}f(0^+)$ vanishes and the transform is $s^{1/2}/(s+1)$. No formal link to the parent is claimed; the statement is also an instance of the platform's proved variant `laplace_rlDeriv_of_contDiffOn` once its hypotheses are checked.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   I. Podlubny, Fractional Differential Equations, Academic Press 1999, Section 2.8 (Laplace transform of fractional derivatives) (cited from memory; section number not verified). Origin of this statement: the explicit case nu = 1/2, f(t) = e^{-t} of the platform theorem FractionalCalc.laplace_rlDeriv (Eq. 21). The identity was checked numerically (mpmath, s = 3 + i/2, numerical derivative of I^{1/2} f): both sides equal 0.432245 - 0.018070 i.

import Mathlib
import Definitions.Def_FractionalCalc_rlIntegral
import Definitions.Def_FractionalCalc_caputoDeriv
import Definitions.Def_FractionalCalc_rlDeriv
import Definitions.Def_FractionalCalc_mittagLeffler
import Definitions.Def_QueueingFundamentals_Transient_laplace

set_option autoImplicit false

open MeasureTheory Set Classical QueueingFundamentals.Transient

namespace LefebvreVariations

/-- **The Riemann–Liouville derivative of order `1/2` of a decaying exponential.** For `f(t) = e^{-t}` and
`Re s > 0`, `L[D^{1/2} f](s) = s^{1/2} F(s) - (I^{1/2} f)(0^+) = s^{1/2}/(s+1)` (principal branch), since the
fractional integral `I^{1/2} e^{-t}` tends to `0` at `0^+`. This is the rule `L[D^ν f] = s^ν F(s) - Σ_{k<n}
s^{n-k-1} (d/dt)^k I^{n-ν} f (0^+)` for Riemann–Liouville derivatives (Podlubny, *Fractional Differential
Equations*, Academic Press 1999, Section 2.8, cited from memory) in the first genuinely fractional case.

**Formalization Note.** `FractionalCalc.rlDeriv 0 (1/2) f = iteratedDeriv 1 (rlIntegral 0 (1/2) f)` (here
`n = ⌊1/2⌋ + 1 = 1`); `laplace` integrates over `(0, ∞)`. -/
theorem laplace_rlDeriv_half_exp (s : ℂ) (hs : 0 < s.re) :
    laplace (FractionalCalc.rlDeriv 0 (1 / 2 : ℝ) (fun t : ℝ => Real.exp (-t))) s =
      s ^ (1 / 2 : ℂ) / (s + 1) := by
  sorry

end LefebvreVariations
