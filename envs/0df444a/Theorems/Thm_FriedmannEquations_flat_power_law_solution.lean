-- Prove2me | Theorems.Thm_FriedmannEquations_flat_power_law_solution
-- name    : FriedmannEquations.flat_power_law_solution
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T22:29:31.613816+00:00
-- url     : https://prove2.me/theorems/ddee9123-53a2-4154-8ae7-be85f1575d9c
-- title:
--   Flat power-law solution $a(t) = a_0\,t^{2/(3(w+1))}$ for $p = w\rho$
-- statement:
--   Let $G>0$, $w\neq -1$ and $a_0>0$, and set $\alpha = \frac{2}{3(w+1)}$. The scale factor $a(t) = a_0\,t^{\alpha}$ together with the density
--   $$\rho(t) = \frac{1}{6\pi G(1+w)^2 t^2}$$
--   and pressure $p = w\rho$ satisfies, at every $t>0$, both Friedmann equations with $k = 0$ and $\Lambda = 0$:
--   $$\Big(\frac{\dot a}{a}\Big)^2 = \frac{8\pi G\rho}{3},\qquad \frac{\ddot a}{a} = -\frac{4\pi G}{3}(\rho+3p).$$
--   (The density is the one forced by the first equation, $\rho = 3H^2/8\pi G$ with $H = \alpha/t$.) The special cases $w=0$ ($a\propto t^{2/3}$, matter) and $w=1/3$ ($a\propto t^{1/2}$, radiation) are the source's examples.
-- source:
--   Wikipedia, "Friedmann equations", revision oldid=1374073387, https://en.wikipedia.org/w/index.php?title=Friedmann_equations&oldid=1374073387 (the PDF supplied with this proposal), section "Useful solutions", p. 8.

import Definitions.Def_FriedmannEquations_Defs
import Mathlib

open FriedmannEquations

theorem FriedmannEquations.flat_power_law_solution
    (G w a₀ : ℝ) (hG : 0 < G) (hw : w ≠ -1) (ha₀ : 0 < a₀) :
    let R : ℝ → ℝ := fun t => a₀ * t ^ (2 / (3 * (w + 1)))
    let ρ : ℝ → ℝ := fun t => 1 / (6 * Real.pi * G * (1 + w) ^ 2 * t ^ 2)
    ∀ t : ℝ, 0 < t →
      FirstFriedmannEq G 0 0 R ρ t ∧ SecondFriedmannEq G 0 R ρ (fun s => w * ρ s) t := by sorry
