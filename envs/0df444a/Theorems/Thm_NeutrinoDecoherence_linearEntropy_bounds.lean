-- Prove2me | Theorems.Thm_NeutrinoDecoherence_linearEntropy_bounds
-- name    : NeutrinoDecoherence.linearEntropy_bounds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T11:35:54.462591+00:00
-- url     : https://prove2.me/theorems/452d7ea3-4990-4b61-b0c3-f6a87657520d
-- title:
--   Bounds on the linear entropy, eq. (2.45)
-- statement:
--   Let $\rho$ be an $n\times n$ density matrix (positive semidefinite, trace one) and let $S_l(\rho) = 1-\operatorname{Tr}(\rho^2)$ be its linear entropy. Then
--   $$0\le S_l(\rho)\le 1,$$
--   and $S_l(\rho)=0$ if and only if $\rho$ is pure, i.e. $\rho^2=\rho$.
--
--   The linear entropy is the purity measure used throughout the thesis to quantify how Open System effects destroy the coherence of a neutrino state.
--
--   **Formalization Note** "Pure" is encoded as idempotence $\rho^2=\rho$, which for a density matrix is equivalent to being a rank-one projector.
-- source:
--   G. F. S. Alves, *Decoherence in Neutrino Oscillations in the IceCube Experiment* (Descoerência em Oscilações de Neutrinos no Experimento IceCube), MSc dissertation, Instituto de Física, Universidade de São Paulo, 2020; supervisor R. Zukanovich Funchal; Section 2.2.3, p. 51, eqs. (2.44)–(2.45).

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs
open Matrix Complex
open scoped ComplexOrder

namespace NeutrinoDecoherence
theorem linearEntropy_bounds {n : Type*} [Fintype n] (ρ : Matrix n n ℂ)
    (hρ : IsDensityMatrix ρ) :
    0 ≤ linearEntropy ρ ∧ linearEntropy ρ ≤ 1 ∧ (linearEntropy ρ = 0 ↔ ρ * ρ = ρ) := by sorry
end NeutrinoDecoherence
