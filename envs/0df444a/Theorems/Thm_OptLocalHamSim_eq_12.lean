-- Prove2me | Theorems.Thm_OptLocalHamSim_eq_12
-- name    : OptLocalHamSim.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:33:48.930312+00:00
-- url     : https://prove2.me/theorems/7628b69b-1829-4513-8871-acd53151341e
-- title:
--   Eq. (12) — $D_{\mathrm{ph}}(z)$ is unitary and $\langle+|D_{\mathrm{ph}}(z)|+\rangle=z$
-- statement:
--   For $z\in\mathbb C$ with $|z|\le1$, let $\phi:=\arg z\in(-\pi,\pi]$ (with $\phi:=0$ at zero) and $\theta:=\arccos|z|$. Then the diagonal matrix
--
--   $$
--   D_{\mathrm{ph}}(z):=\mathrm{diag}\bigl(e^{i(\phi+\theta)},e^{i(\phi-\theta)}\bigr)
--   $$
--
--   is unitary and
--
--   $$
--   \langle+|D_{\mathrm{ph}}(z)|+\rangle=z,\qquad |+\rangle=(|0\rangle+|1\rangle)/\sqrt2 .
--   $$
--
--   A complex number of modulus at most one is thus the average of two phases; the circuit realizes every scalar coefficient factor this way.
--
--   Differences from the source: none.
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), eq. (12), p.12

import Mathlib
import Definitions.Def_OptLocalHamSim_Dph

open scoped Matrix

namespace OptLocalHamSim

/-- **Eq. (12)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.12. For z_c ∈ ℂ with |z_c| ≤ 1, ϕ := arg z_c ∈ (−π, π] (ϕ := 0 at zero) and
θ := arccos |z_c| define a diagonal unitary with the required matrix element:
D_ph(z_c) := diag(e^{i(ϕ+θ)}, e^{i(ϕ−θ)}), ⟨+|D_ph(z_c)|+⟩ = z_c.

**Formalization Note** `⟨+|M|+⟩` is `star plusVec ⬝ᵥ (M *ᵥ plusVec)` with `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
theorem eq_12 (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Dph z ∈ Matrix.unitaryGroup Bool ℂ ∧ star plusVec ⬝ᵥ (Dph z *ᵥ plusVec) = z := by sorry

end OptLocalHamSim
