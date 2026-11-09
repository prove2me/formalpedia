-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_one_step_bounds
-- name    : LeeYangGap.SpectralGap.one_step_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:29.750205+00:00
-- url     : https://prove2.me/theorems/c435e1b4-b73b-4dee-aa94-d0f580d46dde
-- title:
--   Lemma 13 — One-step Trotter bounds
-- statement:
--   Let $H$ be a Lee–Yang Hamiltonian on $n\ge1$ qubits, with all five real bond coefficients satisfying Definition 1, and let $H_h=H-h\sum_iZ_i$ for $h>0$. Let $W=\sum_{ij}w^z_{ij}$ and $\Gamma=3W+nh$. Let $S\subseteq[n]$ be nonempty and $\epsilon>0$. Set $T=e^{-\epsilon H_h}$, $L=\prod_{ij}e^{-\epsilon H_{ij}/2}$, $S_\epsilon=Le^{\epsilon h\sum_iZ_i}L^\dagger$ and $\widetilde Z_S=LZ_SL^{-1}$. If $\epsilon\Gamma\le1/2$, then
--   $$\|S_\epsilon-T\|\le2\epsilon^2\Gamma^2,\qquad \|\widetilde Z_S-Z_S\|\le5\epsilon W.$$
--   Both norms are induced Hilbert-space operator norms. These estimates quantify the step error and insertion error used in the comparison statements.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Lemma 13, printed/PDF p. 17

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem one_step_bounds {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (h : ℝ) (hh : 0 < h) (S : Finset (Fin n)) (hS : S.Nonempty) (ε : ℝ) (hεpos : 0 < ε)
    (hε : ε * gamma B h ≤ 1/2) :
    ‖trotterStep B h ε - mexp ((-ε : ℂ) • fieldHamiltonian B h)‖ ≤
      2 * ε^2 * (gamma B h)^2 ∧
    ‖conjugatedZ B ε S - zProduct S‖ ≤ 5 * ε * weight B := by sorry
end LeeYangGap.SpectralGap
