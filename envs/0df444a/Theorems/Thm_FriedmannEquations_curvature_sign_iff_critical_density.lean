-- Prove2me | Theorems.Thm_FriedmannEquations_curvature_sign_iff_critical_density
-- name    : FriedmannEquations.curvature_sign_iff_critical_density
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T21:57:44.154877+00:00
-- url     : https://prove2.me/theorems/ea01d50c-55f6-4310-ad4b-c02355691a75
-- title:
--   Critical density decides the curvature: $k=0 \iff \rho=\rho_c$, $k>0\iff\rho>\rho_c$, $k<0\iff\rho<\rho_c$ (for $\Lambda=0$)
-- statement:
--   Let $G > 0$, $k\in\mathbb R$, and suppose that at a time $t$ with $R(t)\neq 0$ the first Friedmann equation with vanishing cosmological constant holds:
--   $$H^2 = \frac{8\pi G\rho}{3} - \frac{k}{R^2},\qquad H = \dot R/R.$$
--   With the critical density $\rho_c = \dfrac{3H^2}{8\pi G}$ of this Hubble rate,
--   $$k = 0 \iff \rho = \rho_c,\qquad k > 0 \iff \rho > \rho_c,\qquad k < 0 \iff \rho < \rho_c,$$
--   i.e. critical density gives a flat universe, higher density a closed one ($k>0$) and lower density an open one ($k<0$).
-- source:
--   Wikipedia, "Friedmann equations", revision oldid=1374073387, https://en.wikipedia.org/w/index.php?title=Friedmann_equations&oldid=1374073387 (the PDF supplied with this proposal), sections "Spatial curvature" (pp. 2–3) and "Critical density" (p. 3).

import Definitions.Def_FriedmannEquations_Defs
import Mathlib

open FriedmannEquations

theorem FriedmannEquations.curvature_sign_iff_critical_density
    (G k : ℝ) (hG : 0 < G) (R ρ : ℝ → ℝ) (t : ℝ) (hR : R t ≠ 0)
    (h₁ : FirstFriedmannEq G 0 k R ρ t) :
    (k = 0 ↔ ρ t = criticalDensity G (hubble R t)) ∧
    (0 < k ↔ criticalDensity G (hubble R t) < ρ t) ∧
    (k < 0 ↔ ρ t < criticalDensity G (hubble R t)) := by sorry
