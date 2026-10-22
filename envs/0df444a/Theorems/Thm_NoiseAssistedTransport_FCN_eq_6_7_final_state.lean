-- Prove2me | Theorems.Thm_NoiseAssistedTransport_FCN_eq_6_7_final_state
-- name    : NoiseAssistedTransport.FCN.eq_6_7_final_state
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:12.230146+00:00
-- url     : https://prove2.me/theorems/f38a5c5b-d6e9-457d-8d0b-6ebd81c3d366
-- title:
--   Eqs. (6)–(7), p. 4 — final state (N−2)/(N−1)|Ψ⟩⟨Ψ| + 1/(N−1)|N+1⟩⟨N+1| of the noiseless FCN
-- statement:
--   Consider the noiseless fully connected network of §II.A with $N \ge 3$ sites: zero site energies, hopping $J \ne 0$, no dissipation and no dephasing, the sink coupled to site $N$ with rate $\Gamma_{N+1} > 0$, and the initial state $|1\rangle\langle 1|$. Let
--
--   $$|\Psi\rangle = \frac{1}{\sqrt{(N-1)(N-2)}}\sum_{j \ne N, 1}\bigl(|1\rangle - |j\rangle\bigr),$$
--
--   the sum running over the sites $j = 2,\dots,N-1$. Then, entrywise,
--
--   $$\lim_{t\to\infty}\rho(t) = \frac{N-2}{N-1}\,|\Psi\rangle\langle\Psi| + \frac{1}{N-1}\,|N+1\rangle\langle N+1|.$$
--
--   The weight $\frac{N-2}{N-1}$ is trapped in the invariant subspace by destructive interference, and only $\frac{1}{N-1}$ reaches the sink.
--
--   **Formalization Note** The limit is taken in the (entrywise) topology of complex $(N+2)\times(N+2)$ matrices. The hypotheses $J \ne 0$ and $\Gamma_{N+1} > 0$ are needed: with $J = 0$ the excitation stays on site 1, and with $\Gamma_{N+1} = 0$ nothing reaches the sink. $N \ge 3$ is needed for $|\Psi\rangle$ to be defined.
-- source:
--   Caruso et al., Highly efficient energy excitation transfer in light-harvesting complexes, arXiv:0901.4454v2, p. 4, §II.A, Eqs. (6)–(7); cf. p. 13, final populations after (A22)

import Mathlib
import Definitions.Def_NoiseAssistedTransport_FCN_Model
open scoped Matrix
open Fin.NatCast

namespace NoiseAssistedTransport.FCN

/-- Eqs. (6)–(7), p. 4: the noiseless FCN state started in `|1⟩⟨1|` tends to
`(N − 2)/(N − 1) |Ψ⟩⟨Ψ| + 1/(N − 1) |N + 1⟩⟨N + 1|`. -/
theorem eq_6_7_final_state (N : ℕ) (hN : 3 ≤ N) (J Γs : ℝ) (hJ : J ≠ 0) (hΓs : 0 < Γs) :
    Filter.Tendsto (fcnEvolve N J 0 Γs) Filter.atTop (nhds (finalState N)) := by sorry

end NoiseAssistedTransport.FCN
