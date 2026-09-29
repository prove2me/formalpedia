-- Prove2me | Theorems.Thm_NeutrinoDecoherence_vonNeumannEntropy_bounds
-- name    : NeutrinoDecoherence.vonNeumannEntropy_bounds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T11:47:49.161394+00:00
-- url     : https://prove2.me/theorems/3ffc8d5f-2ab8-40d5-bc7f-3c24e11a5c9b
-- title:
--   Bounds on the von Neumann entropy, eqs. (2.40)–(2.41)
-- statement:
--   Let $\rho$ be a density matrix on $\mathbb C^N$ and $S(\rho)=-\operatorname{Tr}(\rho\ln\rho)$ its von Neumann entropy. Then
--   $$0\le S(\rho)\le \ln N,$$
--   with $S(\rho)=0$ if and only if $\rho$ is pure ($\rho^2=\rho$), and $S(\rho)=\ln N$ if and only if $\rho$ is the maximally mixed state $\rho = \tfrac1N I_N$.
--
--   These are the basic range properties of the entropy used in Appendix B to discuss entropy growth under Open System evolution.
--
--   **Formalization Note** $-x\ln x$ is applied to $\rho$ through the continuous functional calculus, with the usual convention $0\ln 0 = 0$.
-- source:
--   G. F. S. Alves, *Decoherence in Neutrino Oscillations in the IceCube Experiment* (Descoerência em Oscilações de Neutrinos no Experimento IceCube), MSc dissertation, Instituto de Física, Universidade de São Paulo, 2020; supervisor R. Zukanovich Funchal; Section 2.2.3, p. 50, eqs. (2.39)–(2.41).

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs
open Matrix Complex
open scoped ComplexOrder

namespace NeutrinoDecoherence
theorem vonNeumannEntropy_bounds {n : Type*} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ)
    (hρ : IsDensityMatrix ρ) :
    0 ≤ vonNeumannEntropy ρ ∧ vonNeumannEntropy ρ ≤ Real.log (Fintype.card n) ∧
      (vonNeumannEntropy ρ = 0 ↔ ρ * ρ = ρ) ∧
      (vonNeumannEntropy ρ = Real.log (Fintype.card n) ↔
        ρ = ((Fintype.card n : ℂ)⁻¹) • (1 : Matrix n n ℂ)) := by sorry
end NeutrinoDecoherence
