-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_correlation_decay
-- name    : LeeYangGap.SpectralGap.correlation_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:48.472632+00:00
-- url     : https://prove2.me/theorems/4146d367-2e19-4dbf-8a13-1f1add0467a4
-- title:
--   Theorem 10 — Decay of two-point correlations of products
-- statement:
--   Let $H$ be a Lee–Yang Hamiltonian on $n\ge1$ qubits, with all five real bond coefficients satisfying Definition 1, and let $H_h=H-h\sum_iZ_i$ for $h>0$. Let $\beta>0$, $W=\sum_{ij}w^z_{ij}$ and $\Gamma=3W+nh$. For every nonempty $S\subseteq[n]$ let $f_S(t)=\langle Z_S(0)Z_S(t)\rangle_\beta-\langle Z_S\rangle_\beta^2$. Define $C_\star=\max(n,6\beta W)$, $C_T=48(\beta\Gamma^2+W)$, $G=2\max(C_T,\Gamma,h,1)$ and $K=256C_\star G/h+2$. For every real $t\in[0,\beta]$,
--   $$|f_S(t)|\le K e^{-(h/2)\min(t,\beta-t)}.$$
--   The rate is the same for every product $Z_S$, with the source's explicit temperature-dependent prefactor and both endpoints included.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Theorem 10, printed/PDF p. 10

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem correlation_decay {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (h : ℝ) (hh : 0 < h) (β : ℝ) (hβ : 0 < β) (S : Finset (Fin n)) (hS : S.Nonempty) (t : ℝ) (ht : 0 ≤ t) (htβ : t ≤ β) :
    ‖connected B h β S t‖ ≤ decayK B h β * Real.exp (-(h/2) * min t (β-t)) := by sorry
end LeeYangGap.SpectralGap
