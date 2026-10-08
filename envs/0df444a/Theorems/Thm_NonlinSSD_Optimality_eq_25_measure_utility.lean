-- Prove2me | Theorems.Thm_NonlinSSD_Optimality_eq_25_measure_utility
-- name    : NonlinSSD.Optimality.eq_25_measure_utility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:00:32.562721+00:00
-- url     : https://prove2.me/theorems/bb5432b9-ebcc-4afd-91df-26a183e90f6f
-- title:
--   Eq. (25) — the measure integral equals minus expected utility
-- statement:
--   Let $a\le b$, let $\mu$ be a finite nonnegative Borel measure supported on $[a,b]$, and let $X\in\mathcal L^1(\Omega,P)$. Define $u_\mu(t)=-\int_t^b\mu([\tau,b])d\tau$ for $t<b$ and $u_\mu(t)=0$ for $t\ge b$. Then
--   $$\int_{[a,b]}F_2(X;\eta)\,d\mu(\eta)=-\mathbb E[u_\mu(X)].$$
--
--   This identity identifies the measure Lagrangian with a utility Lagrangian and supplies the expected utility complementarity condition in Theorem 2.
--
--   **Formalization Note** The closed interval includes atoms at both endpoints. Finiteness and support of the measure and integrability of $X$ are explicit, preventing a default zero value for a nonintegrable Bochner integral.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), pp. 8–9, Eq. (25), proof of Theorem 2

import Mathlib
import Definitions.Def_NonlinSSD_Optimality_Basic

namespace NonlinSSD.Optimality

open MeasureTheory

/-- Equation (25), p. 9: integration of the second performance function against a
finite nonnegative measure is minus expected utility of the associated function. -/
theorem eq_25_measure_utility
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) (hab : a ≤ b) (μ : Measure ℝ)
    (hfinite : μ Set.univ < ⊤)
    (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (X : Ω → ℝ) (hX : Integrable X P) :
    (∫ η in Set.Icc a b, F2 P X η ∂μ) =
      -(∫ ω, uOfMeasure μ b (X ω) ∂P) := by sorry

end NonlinSSD.Optimality
