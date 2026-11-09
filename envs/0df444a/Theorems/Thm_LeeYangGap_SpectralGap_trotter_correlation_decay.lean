-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_trotter_correlation_decay
-- name    : LeeYangGap.SpectralGap.trotter_correlation_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:12.056831+00:00
-- url     : https://prove2.me/theorems/a1091069-fd17-43b1-809d-9b6183ac3969
-- title:
--   Proposition 8 — Decay of the Trotterized correlation function
-- statement:
--   Let $H$ be a Lee–Yang Hamiltonian on $n\ge1$ qubits, with all five real bond coefficients satisfying Definition 1, and let $H_h=H-h\sum_iZ_i$ for $h>0$. Let $\beta>0$, $W=\sum_{ij}w^z_{ij}$ and $\Gamma=3W+nh$. For a nonempty $S\subseteq[n]$, put $Z_S=\prod_{i\in S}Z_i$. For an integer $M\ge2$ put $\epsilon=\beta/M$; the layer $k$ satisfies $1\le k<M$. All Trotter quantities are computed from the ordered product $L=\prod_{ij}e^{-\epsilon H_{ij}/2}$ and the cyclic trace polynomial. Put $C_\star=\max(n,6\beta W)$ and $d_k=\min(k,M-k)+1$. If $\epsilon h\le2$, then
--   $$|f_{S,\epsilon}(k)|\le\frac{128C_\star}{\epsilon h}e^{-\epsilon h d_k}.$$
--   The estimate includes the full cyclic layer distance and its additive one, with the exact source prefactor.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Proposition 8, printed/PDF p. 9

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem trotter_correlation_decay {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (h : ℝ) (hh : 0 < h) (β : ℝ) (hβ : 0 < β) (S : Finset (Fin n)) (hS : S.Nonempty) (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (hk : 1 ≤ k) (hkM : k < M)
    (hε : stepSize β M * h ≤ 2) :
    ‖trotterConnected B h β M S k‖ ≤
      128 * cStar B β / (stepSize β M * h) *
        Real.exp (-stepSize β M * h * layerDistance M k) := by sorry
end LeeYangGap.SpectralGap
