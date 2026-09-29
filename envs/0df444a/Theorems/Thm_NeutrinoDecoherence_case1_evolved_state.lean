-- Prove2me | Theorems.Thm_NeutrinoDecoherence_case1_evolved_state
-- name    : NeutrinoDecoherence.case1_evolved_state
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T13:05:49.055789+00:00
-- url     : https://prove2.me/theorems/d9204c4d-7f88-4d1a-91ce-a1d9693c9612
-- title:
--   Evolved muon-neutrino state under the case (1) Dissipator, eq. (3.23)
-- statement:
--   Let $\theta,\alpha\in\mathbb R$, $E>0$, $\Delta m^2\in\mathbb R$, $\gamma\ge0$ and write $\Delta=\Delta m^2/2E$. Let $t\mapsto\rho(t)$, $t\ge 0$, solve the Lindblad equation with the two-flavour Hamiltonian $H=\operatorname{diag}(0,\Delta)$ and the case (1) Kossakowski matrix $a=\operatorname{diag}(0,0,\gamma)$, with initial state $\rho(0)=\rho_\mu(0)$ from eq. (3.14). Then for every $L\ge0$
--   $$\rho(L)=\begin{pmatrix}\cos^2\theta & e^{-2\gamma L+i(\alpha+\Delta L)}\cos\theta\sin\theta\\ e^{-2\gamma L-i(\alpha+\Delta L)}\cos\theta\sin\theta & \sin^2\theta\end{pmatrix}.$$
--
--   Only the coherences are damped: this is the decoherence mechanism behind the main theorem.
--
--   **Formalization Note** The printed eq. (3.23) carries an overall minus sign on the off-diagonal entries, which is inconsistent with the initial condition (3.14) at $L=0$ and with (3.24); the draft omits it. Time and baseline are identified ($t\to L$, natural units).
-- source:
--   G. F. S. Alves, *Decoherence in Neutrino Oscillations in the IceCube Experiment* (Descoerência em Oscilações de Neutrinos no Experimento IceCube), MSc dissertation, Instituto de Física, Universidade de São Paulo, 2020; supervisor R. Zukanovich Funchal; Section 3.2.2, p. 62, eq. (3.23); Table 3.1 case (1), p. 59; eqs. (3.9), (3.13)–(3.14). Sign of the off-diagonal entries corrected, see Formalization Note.

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs
open Matrix Complex
open scoped ComplexOrder

namespace NeutrinoDecoherence
theorem case1_evolved_state (θ α Δm2 E γ : ℝ) (hE : 0 < E) (hγ : 0 ≤ γ)
    (ρ : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hsol : IsLindbladSolution (twoFlavourHamiltonian Δm2 E)
      (Matrix.diagonal ![0, 0, (γ : ℂ)]) ρ)
    (h0 : ρ 0 = muonInitialState θ α) (L : ℝ) (hL : 0 ≤ L) :
    ρ L = !![((Real.cos θ ^ 2 : ℝ) : ℂ),
        exp (((-2 * γ * L : ℝ) : ℂ) + ((α + Δm2 / (2 * E) * L : ℝ) : ℂ) * I) *
          ((Real.cos θ * Real.sin θ : ℝ) : ℂ);
        exp (((-2 * γ * L : ℝ) : ℂ) - ((α + Δm2 / (2 * E) * L : ℝ) : ℂ) * I) *
          ((Real.cos θ * Real.sin θ : ℝ) : ℂ),
        ((Real.sin θ ^ 2 : ℝ) : ℂ)] := by sorry
end NeutrinoDecoherence
