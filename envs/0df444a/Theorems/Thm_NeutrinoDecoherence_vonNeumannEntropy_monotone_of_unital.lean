-- Prove2me | Theorems.Thm_NeutrinoDecoherence_vonNeumannEntropy_monotone_of_unital
-- name    : NeutrinoDecoherence.vonNeumannEntropy_monotone_of_unital
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T12:09:08.752915+00:00
-- url     : https://prove2.me/theorems/6d9357fc-d61e-4644-9a92-a7fcccaf874f
-- title:
--   Entropy increase when the maximally mixed state is a fixed point, App. B.1
-- statement:
--   Let $H$ be a Hermitian $2\times2$ matrix and $a$ a positive semidefinite $3\times3$ Kossakowski matrix whose Dissipator annihilates the identity, $D[I]=0$ (equivalently, the maximally mixed state $\frac12 I$ is a fixed point of $D$). Let $t\mapsto\rho(t)$, $t\ge0$, solve the Lindblad equation
--   $$\dot\rho(t) = -i[H,\rho(t)] + D[\rho(t)]$$
--   with $\rho(0)$ a density matrix. Then the von Neumann entropy $t\mapsto S(\rho(t))$ is non-decreasing on $[0,\infty)$.
--
--   This is the physical-consistency criterion that the thesis imposes on Dissipators in Section 3.1 (first column of the vectorized Dissipator equal to zero).
--
--   **Formalization Note** The thesis argues for general dimension $N$; the draft states the two-level case, which is the setting of the rest of the mission. Positive semidefiniteness of $a$ (conditions 1)–3) of Section 2.2.2) is what makes the evolution completely positive.
-- source:
--   G. F. S. Alves, *Decoherence in Neutrino Oscillations in the IceCube Experiment* (Descoerência em Oscilações de Neutrinos no Experimento IceCube), MSc dissertation, Instituto de Física, Universidade de São Paulo, 2020; supervisor R. Zukanovich Funchal; Appendix B.1, pp. 117–118, eqs. (B.1)–(B.5); Section 3.1, p. 57; Section 2.2.2, p. 49 (conditions 1)–3)).

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs
open Matrix Complex
open scoped ComplexOrder

namespace NeutrinoDecoherence
theorem vonNeumannEntropy_monotone_of_unital (H : Matrix (Fin 2) (Fin 2) ℂ)
    (a : Matrix (Fin 3) (Fin 3) ℂ) (hH : H.IsHermitian) (ha : a.PosSemidef)
    (hunital : dissipator a 1 = 0) (ρ : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hsol : IsLindbladSolution H a ρ) (h0 : IsDensityMatrix (ρ 0)) :
    MonotoneOn (fun t => vonNeumannEntropy (ρ t)) (Set.Ici 0) := by sorry
end NeutrinoDecoherence
