-- Prove2me | Theorems.Thm_FriedmannEquations_first_friedmann_density_parameters
-- name    : FriedmannEquations.first_friedmann_density_parameters
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T22:25:00.612272+00:00
-- url     : https://prove2.me/theorems/d989cbe9-44e2-42df-86f4-82ff0f462b92
-- title:
--   First Friedmann equation in density parameters: $H^2/H_0^2 = \Omega_{0,R}a^{-4} + \Omega_{0,M}a^{-3} + \Omega_{0,k}a^{-2} + \Omega_{0,\Lambda}$
-- statement:
--   Let $G>0$ and $\Lambda,k\in\mathbb R$; let $t_0$ ("today") and $t$ be times with $R(t_0)\ne 0$, $R(t)\ne0$ and $H_0 := H(t_0)\neq 0$, and let $a = R(t)/R(t_0)$. Suppose the density consists of radiation and matter, $\rho(s) = \rho_R\,a(s)^{-4} + \rho_M\,a(s)^{-3}$ for all $s$ (with $a(s)=R(s)/R(t_0)$), and that the first Friedmann equation $H^2 = \frac{8\pi G\rho}{3} - \frac{k}{R^2} + \frac{\Lambda}{3}$ holds at $t$ and at $t_0$. With the present-day density parameters
--   $$\Omega_{0,R} = \frac{\rho_R}{\rho_c},\quad \Omega_{0,M} = \frac{\rho_M}{\rho_c},\quad \Omega_{0,\Lambda} = \frac{\Lambda/(8\pi G)}{\rho_c} = \frac{\Lambda}{3H_0^2},\quad \Omega_{0,k} = 1 - \Omega_0,\ \ \Omega_0 = \Omega_{0,R}+\Omega_{0,M}+\Omega_{0,\Lambda},$$
--   where $\rho_c = 3H_0^2/(8\pi G)$, one has
--   $$\frac{H(t)^2}{H_0^2} = \Omega_{0,R}a^{-4} + \Omega_{0,M}a^{-3} + \Omega_{0,k}a^{-2} + \Omega_{0,\Lambda}.$$
--   Here the vacuum energy is counted in the total $\Omega_0$ (vacuum density $\Lambda/8\pi G$, cf. section *Cosmological constant*).
-- source:
--   Wikipedia, "Friedmann equations", revision oldid=1374073387, https://en.wikipedia.org/w/index.php?title=Friedmann_equations&oldid=1374073387 (the PDF supplied with this proposal), section "Density parameter", p. 5 (display after "in terms of the present values of the density parameters").

import Definitions.Def_FriedmannEquations_Defs
import Mathlib

open FriedmannEquations

theorem FriedmannEquations.first_friedmann_density_parameters
    (G Λ k ρR ρM : ℝ) (hG : 0 < G) (R ρ : ℝ → ℝ) (t t₀ : ℝ)
    (hR : R t ≠ 0) (hR₀ : R t₀ ≠ 0) (hH₀ : hubble R t₀ ≠ 0)
    (hρ : ∀ s, ρ s = ρR / (R s / R t₀) ^ 4 + ρM / (R s / R t₀) ^ 3)
    (h₁ : FirstFriedmannEq G Λ k R ρ t) (h₁₀ : FirstFriedmannEq G Λ k R ρ t₀) :
    let a := R t / R t₀
    let H₀ := hubble R t₀
    let ΩR := densityParameter G H₀ ρR
    let ΩM := densityParameter G H₀ ρM
    let ΩΛ := densityParameter G H₀ (Λ / (8 * Real.pi * G))
    let Ωk := 1 - (ΩR + ΩM + ΩΛ)
    hubble R t ^ 2 / H₀ ^ 2 =
      ΩR * a ^ (-4 : ℤ) + ΩM * a ^ (-3 : ℤ) + Ωk * a ^ (-2 : ℤ) + ΩΛ := by sorry
