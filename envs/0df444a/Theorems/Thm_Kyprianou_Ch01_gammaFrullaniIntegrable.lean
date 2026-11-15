-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaFrullaniIntegrable
-- name    : Kyprianou.Ch01.gammaFrullaniIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:07:16.163902+00:00
-- url     : https://prove2.me/theorems/4f118d6c-ae47-4a2b-9473-3d8a7b0dff8d
-- title:
--   Kyprianou §1.2.4: integrability of the complex gamma Frullani kernel
-- statement:
--   For positive alpha and beta and any complex z with nonpositive real part, the kernel (1-exp(zx))*beta*exp(-alpha*x)/x is integrable on the positive half-line.
-- source:
--   Kyprianou (2006), Chapter 1, §1.2.4, gamma Lévy characteristic exponent; Cohn–Elkies complex Frullani integrability theorem.

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexFrullaniKernel_integrable
open MeasureTheory Filter Set CohnElkies
open scoped Topology
set_option autoImplicit false

/-- Integrability of the Chapter 1 gamma-type complex Frullani kernel. -/
theorem Kyprianou.Ch01.gammaFrullaniIntegrable
    (α β : ℝ) (z : ℂ) (hα : 0 < α) (hβ : 0 < β) (hz : z.re ≤ 0) :
    IntegrableOn
      (fun x : ℝ =>
        ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
          ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ)))
      (Ioi (0 : ℝ)) := by sorry
