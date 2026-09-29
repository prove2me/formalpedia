-- Prove2me | Theorems.Thm_NeutrinoDecoherence_energy_conservation_iff
-- name    : NeutrinoDecoherence.energy_conservation_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T12:59:08.676283+00:00
-- url     : https://prove2.me/theorems/ef0db339-d646-4f2f-a546-de43c95594a4
-- title:
--   Average-energy conservation forces the Dissipator of case (1), eqs. (3.19)–(3.22)
-- statement:
--   Fix $E>0$ and $\Delta m^2\ne0$, let $H=\operatorname{diag}(0,\Delta m^2/2E)$ be the two-flavour Hamiltonian in the mass basis, and let $a$ be a positive semidefinite $3\times3$ Kossakowski matrix. Then the average energy is stationary along the Lindblad flow for every state,
--   $$\operatorname{Tr}\bigl(H\,\mathcal L[\rho]\bigr)=0\quad\text{for every density matrix }\rho,$$
--   if and only if
--   $$a=\begin{pmatrix}0&0&0\\0&0&0\\0&0&\gamma\end{pmatrix}\quad\text{for some real }\gamma,$$
--   i.e. the Dissipator is that of case (1) with $\gamma=a_{33}$.
--
--   This identifies case (1), the pure-decoherence Dissipator used for the mission's main theorem, as the unique energy-conserving choice.
--
--   **Formalization Note** "Conserved for all times" is encoded as $\operatorname{Tr}(H\dot\rho)=0$ at every density matrix, which is what conservation along every trajectory amounts to. The statement is at a single fixed energy.
-- source:
--   G. F. S. Alves, *Decoherence in Neutrino Oscillations in the IceCube Experiment* (Descoerência em Oscilações de Neutrinos no Experimento IceCube), MSc dissertation, Instituto de Física, Universidade de São Paulo, 2020; supervisor R. Zukanovich Funchal; Section 3.2.1, pp. 58–60, eqs. (3.11)–(3.12), (3.18)–(3.22); Table 3.1, p. 59.

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs
open Matrix Complex
open scoped ComplexOrder

namespace NeutrinoDecoherence
theorem energy_conservation_iff (Δm2 E : ℝ) (hE : 0 < E) (hΔ : Δm2 ≠ 0)
    (a : Matrix (Fin 3) (Fin 3) ℂ) (ha : a.PosSemidef) :
    (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix ρ →
        (twoFlavourHamiltonian Δm2 E *
          lindbladian (twoFlavourHamiltonian Δm2 E) a ρ).trace = 0) ↔
      ∃ γ : ℝ, a = Matrix.diagonal ![0, 0, (γ : ℂ)] := by sorry
end NeutrinoDecoherence
