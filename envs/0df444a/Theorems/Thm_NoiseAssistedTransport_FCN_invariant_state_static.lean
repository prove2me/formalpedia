-- Prove2me | Theorems.Thm_NoiseAssistedTransport_FCN_invariant_state_static
-- name    : NoiseAssistedTransport.FCN.invariant_state_static
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:04.756839+00:00
-- url     : https://prove2.me/theorems/5c45aa92-dc35-4524-b580-053935020dab
-- title:
--   §II.A, p. 4 — an invariant state has no dynamics and p_sink = 0
-- statement:
--   Consider the noiseless fully connected network of §II.A: $N$ sites, zero site energies, hopping $J$, no dissipation ($\Gamma_j = 0$), no dephasing ($\gamma_j = 0$), and the sink coupled to site $N$ with rate $\Gamma_{N+1}$. Let $v$ be an eigenvector of the Hamiltonian, $Hv = Ev$, with no overlap with site $N$, $\langle N|v\rangle = 0$. If the system is started in $\rho_0 = |v\rangle\langle v|$, then for every time $t$
--
--   $$\rho(t) = |v\rangle\langle v| \qquad\text{and}\qquad p_{\rm sink}(t) = 0.$$
--
--   This is the paper's observation that an invariant state (a state that is an eigenstate of $H$ and has no overlap with site $N$) is completely trapped in a noise-protected stationary state, so that $p_{\rm sink}(\infty) = 0$.
--
--   **Formalization Note** The vector $v$ need not be normalized; $|v\rangle\langle v|$ is `Matrix.vecMulVec v (star v)`. The statement holds for every time $t$, which in particular gives $p_{\rm sink}(\infty) = 0$.
-- source:
--   Caruso et al., Highly efficient energy excitation transfer in light-harvesting complexes, arXiv:0901.4454v2, p. 4, §II.A (definition of the invariant subspace and 'if the system is initially prepared in one of the invariant states, then there are no dynamics')

import Mathlib
import Definitions.Def_NoiseAssistedTransport_FCN_Model
open scoped Matrix
open Fin.NatCast

namespace NoiseAssistedTransport.FCN

/-- §II.A, p. 4: in the noiseless FCN an eigenstate of `H` with no overlap with site `N` has no
dynamics, and no population reaches the sink. -/
theorem invariant_state_static (N : ℕ) (J Γs : ℝ) (E : ℂ) (v : Fin (N + 2) → ℂ)
    (hv : hamiltonian N (fun _ => 0) J *ᵥ v = E • v) (hvN : v ((N : ℕ) : Fin (N + 2)) = 0)
    (t : ℝ) :
    evolve N (fun _ => 0) (fun _ => 0) (fun _ => 0) J Γs N (pureState v) t = pureState v ∧
    sinkPop N (fun _ => 0) (fun _ => 0) (fun _ => 0) J Γs N (pureState v) t = 0 := by sorry

end NoiseAssistedTransport.FCN
