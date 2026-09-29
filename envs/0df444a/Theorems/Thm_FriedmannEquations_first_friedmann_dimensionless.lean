-- Prove2me | Theorems.Thm_FriedmannEquations_first_friedmann_dimensionless
-- name    : FriedmannEquations.first_friedmann_dimensionless
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T22:19:25.169517+00:00
-- url     : https://prove2.me/theorems/bb8f9d10-bb7d-479c-9f8a-8fa3b0b34696
-- title:
--   First Friedmann equation in the dimensionless scale factor: $H^2 = (\dot a/a)^2 = \frac{8\pi G}{3}\big[\rho + \frac{\rho_c-\rho_0}{a^2}\big]$
-- statement:
--   Let $G>0$, $k\in\mathbb R$, and let $t_0$ ("now") and $t$ be times with $R(t_0)\ne0$, $R(t)\neq 0$. Suppose the first Friedmann equation with $\Lambda = 0$,
--   $H^2 = \frac{8\pi G\rho}{3} - \frac{k}{R^2}$, holds at both $t$ and $t_0$ (same $k$). Put $a(s) = R(s)/R(t_0)$, $H_0 = H(t_0)$, $\rho_0 = \rho(t_0)$ and $\rho_c = 3H_0^2/(8\pi G)$. Then $\dot a(t)/a(t) = H(t)$ and
--   $$\Big(\frac{\dot a(t)}{a(t)}\Big)^2 = \frac{8\pi G}{3}\left[\rho(t) + \frac{\rho_c - \rho_0}{a(t)^2}\right].$$
-- source:
--   Wikipedia, "Friedmann equations", revision oldid=1374073387, https://en.wikipedia.org/w/index.php?title=Friedmann_equations&oldid=1374073387 (the PDF supplied with this proposal), section "Dimensionless scale factor", p. 3.

import Definitions.Def_FriedmannEquations_Defs
import Mathlib

open FriedmannEquations

theorem FriedmannEquations.first_friedmann_dimensionless
    (G k : ℝ) (hG : 0 < G) (R ρ : ℝ → ℝ) (t t₀ : ℝ) (hR : R t ≠ 0) (hR₀ : R t₀ ≠ 0)
    (h₁ : FirstFriedmannEq G 0 k R ρ t) (h₁₀ : FirstFriedmannEq G 0 k R ρ t₀) :
    hubble (fun s => R s / R t₀) t = hubble R t ∧
    hubble (fun s => R s / R t₀) t ^ 2 =
      8 * Real.pi * G / 3 *
        (ρ t + (criticalDensity G (hubble R t₀) - ρ t₀) / (R t / R t₀) ^ 2) := by sorry
