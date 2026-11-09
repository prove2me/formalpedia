-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_sign_flip_correlator
-- name    : LeeYangGap.SpectralGap.sign_flip_correlator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:44.078875+00:00
-- url     : https://prove2.me/theorems/ac79da3c-7a04-4ed9-81b5-d5d4e89a8b71
-- title:
--   Lemma 4 — Correlator through sign flips
-- statement:
--   Let $H$ be a Lee–Yang Hamiltonian on $n\ge1$ qubits, with all five real bond coefficients satisfying Definition 1, and let $H_h=H-h\sum_iZ_i$ for $h>0$. Let $\beta>0$, $W=\sum_{ij}w^z_{ij}$ and $\Gamma=3W+nh$. For a nonempty $S\subseteq[n]$, put $Z_S=\prod_{i\in S}Z_i$. For an integer $M\ge2$ put $\epsilon=\beta/M$; the layer $k$ satisfies $1\le k<M$. All Trotter quantities are computed from the ordered product $L=\prod_{ij}e^{-\epsilon H_{ij}/2}$ and the cyclic trace polynomial. For the constant point $y_\star=e^{-2\epsilon h}\mathbf1$ and the reflection $\sigma_m$ flipping the signs of $y_{i,m}$ precisely for $i\in S$,
--   $$f_{S,\epsilon}(k)=\frac{\mathcal Z_\epsilon(\sigma_0\sigma_k y_\star)}{\mathcal Z_\epsilon(y_\star)}-\frac{\mathcal Z_\epsilon(\sigma_0 y_\star)}{\mathcal Z_\epsilon(y_\star)}\frac{\mathcal Z_\epsilon(\sigma_k y_\star)}{\mathcal Z_\epsilon(y_\star)}.$$
--   This identity represents the connected correlator by evaluations of the same full layer polynomial, including both distinct single-reflection factors.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Lemma 4, printed/PDF p. 6

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem sign_flip_correlator {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (h : ℝ) (hh : 0 < h) (β : ℝ) (hβ : 0 < β) (S : Finset (Fin n)) (hS : S.Nonempty) (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (hk : 1 ≤ k) (hkM : k < M) :
    let y : LayerVariables n M := starPoint h β
    trotterConnected B h β M S k =
      trotterPartition B β M (reflectLayer S 0 (reflectLayer S k y)) / trotterPartition B β M y -
      (trotterPartition B β M (reflectLayer S 0 y) / trotterPartition B β M y) *
      (trotterPartition B β M (reflectLayer S k y) / trotterPartition B β M y) := by sorry
end LeeYangGap.SpectralGap
