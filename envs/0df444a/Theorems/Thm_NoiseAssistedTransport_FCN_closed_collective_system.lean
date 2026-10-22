-- Prove2me | Theorems.Thm_NoiseAssistedTransport_FCN_closed_collective_system
-- name    : NoiseAssistedTransport.FCN.closed_collective_system
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:09.714403+00:00
-- url     : https://prove2.me/theorems/397d5bb9-6169-46b8-9c07-a661552dd351
-- title:
--   Appendix A.1, p. 12 — closed system of equations for Λ, X, Y, ρ_NN, ρ_00, p_sink
-- statement:
--   Consider the fully connected network of Appendix A.1 with $N \ge 1$ sites, uniform site energy $\omega_j = \omega$, uniform dissipation $\Gamma_j = \Gamma$, uniform dephasing $\gamma_j = \gamma$, hopping $J$, the sink coupled to site $N$ with rate $\Gamma_{N+1}$, and the initial state $|1\rangle\langle 1|$. Define the collective variables (A2), (A8)
--
--   $$\Lambda = \sum_{i,j=1}^N \rho_{ij}, \qquad X + iY = R_N = \sum_{j=1}^N \rho_{Nj},$$
--
--   together with $\rho_{NN}$, $\rho_{00}$ and $p_{\rm sink}$. Then at every time these functions are differentiable and satisfy
--
--   $$\begin{aligned}
--   \dot\Lambda &= -2(\Gamma+\gamma)\Lambda - 2\Gamma_{N+1}X + 2\gamma(1 - \rho_{00} - p_{\rm sink}),\\
--   \dot X &= -(2\Gamma + 2\gamma + \Gamma_{N+1})X + (2\gamma - \Gamma_{N+1})\rho_{NN} - JNY,\\
--   \dot Y &= -(2\Gamma + 2\gamma + \Gamma_{N+1})Y + JNX - J\Lambda,\\
--   \dot\rho_{NN} &= -2(\Gamma + \Gamma_{N+1})\rho_{NN} - 2JY,\\
--   \dot\rho_{00} &= 2\Gamma(1 - \rho_{00} - p_{\rm sink}),\\
--   \dot p_{\rm sink} &= 2\Gamma_{N+1}\rho_{NN}.
--   \end{aligned}$$
--
--   These six linear equations form a closed system; with the initial conditions $\Lambda = 1$, $X = Y = \rho_{NN} = \rho_{00} = p_{\rm sink} = 0$ they determine the sink population, and they are the basis of the exact solutions in Appendix A.2 and A.3.
--
--   **Formalization Note** $\Lambda$, $\rho_{NN}$ and $\rho_{00}$ are taken as real parts of the corresponding complex sums and entries (they are real), and $X$, $Y$ are the real and imaginary parts of $R_N$. The rates are arbitrary real numbers; the identities are algebraic and do not use their signs. The site energy $\omega$ does not enter the equations.
-- source:
--   Caruso et al., Highly efficient energy excitation transfer in light-harvesting complexes, arXiv:0901.4454v2, p. 12, Appendix A.1, the closed system after Eq. (A8); definitions (A2), p. 11, and (A8), p. 12

import Mathlib
import Definitions.Def_NoiseAssistedTransport_FCN_Model
open scoped Matrix
open Fin.NatCast

namespace NoiseAssistedTransport.FCN

/-- Appendix A.1, p. 12: for the FCN with uniform `ω_j = ω`, `Γ_j = Γ`, `γ_j = γ`, sink at
site `N`, started in `|1⟩⟨1|`, the collective variables `Λ = Σ_{i,j=1}^{N} ρ_ij`,
`X + iY = R_N = Σ_{j=1}^{N} ρ_Nj`, `ρ_NN`, `ρ_00` and `p_sink` obey a closed linear system. -/
theorem closed_collective_system (N : ℕ) (hN : 1 ≤ N) (ω Γ γ J Γs : ℝ) (t : ℝ) :
    let ρ : ℝ → Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ := fun s =>
      evolve N (fun _ => ω) (fun _ => Γ) (fun _ => γ) J Γs N (initState N) s
    let Λ : ℝ → ℝ := fun s =>
      (∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
        ρ s ((i : ℕ) : Fin (N + 2)) ((j : ℕ) : Fin (N + 2))).re
    let R : ℝ → ℂ := fun s => ∑ j ∈ Finset.Icc 1 N, ρ s ((N : ℕ) : Fin (N + 2)) ((j : ℕ) : Fin (N + 2))
    let X : ℝ → ℝ := fun s => (R s).re
    let Y : ℝ → ℝ := fun s => (R s).im
    let ρNN : ℝ → ℝ := fun s => (ρ s ((N : ℕ) : Fin (N + 2)) ((N : ℕ) : Fin (N + 2))).re
    let ρ00 : ℝ → ℝ := fun s => (ρ s 0 0).re
    let p : ℝ → ℝ := sinkPop N (fun _ => ω) (fun _ => Γ) (fun _ => γ) J Γs N (initState N)
    HasDerivAt Λ (-2 * (Γ + γ) * Λ t - 2 * Γs * X t + 2 * γ * (1 - ρ00 t - p t)) t ∧
    HasDerivAt X (-(2 * Γ + 2 * γ + Γs) * X t + (2 * γ - Γs) * ρNN t - J * N * Y t) t ∧
    HasDerivAt Y (-(2 * Γ + 2 * γ + Γs) * Y t + J * N * X t - J * Λ t) t ∧
    HasDerivAt ρNN (-2 * (Γ + Γs) * ρNN t - 2 * J * Y t) t ∧
    HasDerivAt ρ00 (2 * Γ * (1 - ρ00 t - p t)) t ∧
    HasDerivAt p (2 * Γs * ρNN t) t := by sorry

end NoiseAssistedTransport.FCN
