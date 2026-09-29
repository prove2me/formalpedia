-- Prove2me | Theorems.Thm_NeutrinoDecoherence_case4_population
-- name    : NeutrinoDecoherence.case4_population
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T13:22:11.724412+00:00
-- url     : https://prove2.me/theorems/a2f71c1c-09d0-4091-9864-f56591205a07
-- title:
--   Population of the evolved state under the case (4) Dissipator, eq. (3.26)
-- statement:
--   Let $\theta,\alpha\in\mathbb R$, $E>0$, $\Delta m^2\in\mathbb R$, $\gamma\ge0$. Let $t\mapsto\rho(t)$, $t\ge0$, solve the Lindblad equation with $H=\operatorname{diag}(0,\Delta m^2/2E)$ and the case (4) Kossakowski matrix $a=\operatorname{diag}(0,\gamma,0)$, starting from $\rho(0)=\rho_\mu(0)$. Then for every $L\ge0$ the first diagonal entry is
--   $$\rho^{11}(L)=\frac{1+e^{-2\gamma L}\cos2\theta}{2}.$$
--
--   Unlike case (1), this Dissipator also relaxes the populations, driving the state towards the maximally mixed one.
--
--   **Formalization Note** $\gamma$ plays the role of $a_{22}$.
-- source:
--   G. F. S. Alves, *Decoherence in Neutrino Oscillations in the IceCube Experiment* (Descoerência em Oscilações de Neutrinos no Experimento IceCube), MSc dissertation, Instituto de Física, Universidade de São Paulo, 2020; supervisor R. Zukanovich Funchal; Section 3.2.2, p. 65, eq. (3.26); Table 3.1 case (4), p. 59.

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs
open Matrix Complex
open scoped ComplexOrder

namespace NeutrinoDecoherence
theorem case4_population (θ α Δm2 E γ : ℝ) (hE : 0 < E) (hγ : 0 ≤ γ)
    (ρ : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hsol : IsLindbladSolution (twoFlavourHamiltonian Δm2 E)
      (Matrix.diagonal ![0, (γ : ℂ), 0]) ρ)
    (h0 : ρ 0 = muonInitialState θ α) (L : ℝ) (hL : 0 ≤ L) :
    ρ L 0 0 = (((1 + Real.exp (-2 * γ * L) * Real.cos (2 * θ)) / 2 : ℝ) : ℂ) := by sorry
end NeutrinoDecoherence
