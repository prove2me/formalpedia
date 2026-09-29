-- Prove2me | Theorems.Thm_NeutrinoDecoherence_survival_probability_case1
-- name    : NeutrinoDecoherence.survival_probability_case1
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T13:52:02.415995+00:00
-- url     : https://prove2.me/theorems/869630fb-d856-4c76-baf4-269ab47b57f5
-- title:
--   Decoherent two-flavour $\nu_\mu$ survival probability, eq. (3.24)
-- statement:
--   Consider two-flavour neutrino oscillations in vacuum treated as an open quantum system. Let $\theta$ be the mixing angle, $\alpha$ the Majorana phase, $E>0$ the neutrino energy, $\Delta m^2$ the mass-squared difference and $\gamma\ge0$ the decoherence parameter. Let $t\mapsto\rho(t)$, $t\ge0$, be a solution of the Lindblad equation
--   $$\dot\rho=-i[H,\rho]+D[\rho],\qquad H=\begin{pmatrix}0&0\\0&\frac{\Delta m^2}{2E}\end{pmatrix},$$
--   whose Dissipator $D$ is built from the case (1) Kossakowski matrix $a=\operatorname{diag}(0,0,\gamma)$, with initial state the muon-neutrino state $\rho(0)=\rho_\mu(0)=U^\dagger|\nu_1\rangle\langle\nu_1|U$. Then for every baseline $L\ge0$ the survival probability $P_{\nu_\mu\to\nu_\mu}=\operatorname{Tr}\{\rho(L)\,\rho_\mu(0)\}$ equals
--   $$P_{\nu_\mu\to\nu_\mu}=\frac14\Bigl(3+\cos4\theta+2e^{-2\gamma L}\cos\Bigl(\frac{\Delta m^2}{2E}L\Bigr)\sin^22\theta\Bigr).$$
--
--   The standard vacuum formula is recovered at $\gamma=0$, and the result is independent of the Majorana phase $\alpha$.
--
--   **Formalization Note** Time and baseline are identified ($t\to L$, natural units). The survival probability is the real part of the trace in (1.11).
-- source:
--   G. F. S. Alves, *Decoherence in Neutrino Oscillations in the IceCube Experiment* (Descoerência em Oscilações de Neutrinos no Experimento IceCube), MSc dissertation, Instituto de Física, Universidade de São Paulo, 2020; supervisor R. Zukanovich Funchal; Section 3.2.2, p. 62, eq. (3.24); with eqs. (1.11), (3.4), (3.9), (3.13)–(3.14) and Table 3.1 case (1).

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs
open Matrix Complex
open scoped ComplexOrder

namespace NeutrinoDecoherence
theorem survival_probability_case1 (θ α Δm2 E γ : ℝ) (hE : 0 < E) (hγ : 0 ≤ γ)
    (ρ : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hsol : IsLindbladSolution (twoFlavourHamiltonian Δm2 E)
      (Matrix.diagonal ![0, 0, (γ : ℂ)]) ρ)
    (h0 : ρ 0 = muonInitialState θ α) (L : ℝ) (hL : 0 ≤ L) :
    transitionProbability (ρ L) (muonInitialState θ α) =
      (3 + Real.cos (4 * θ) +
        2 * Real.exp (-2 * γ * L) * Real.cos (Δm2 / (2 * E) * L) *
          Real.sin (2 * θ) ^ 2) / 4 := by sorry
end NeutrinoDecoherence
