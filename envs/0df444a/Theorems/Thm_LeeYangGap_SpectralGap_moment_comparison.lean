-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_moment_comparison
-- name    : LeeYangGap.SpectralGap.moment_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:29.626057+00:00
-- url     : https://prove2.me/theorems/19e9859f-b2c7-44c0-8df1-8844145fc9c6
-- title:
--   Lemma 17 — Moment comparison
-- statement:
--   Let $H$ be a Lee–Yang Hamiltonian on $n\ge1$ qubits, with all five real bond coefficients satisfying Definition 1, and let $H_h=H-h\sum_iZ_i$ for $h>0$. Let $\beta>0$, $W=\sum_{ij}w^z_{ij}$ and $\Gamma=3W+nh$. For a nonempty $S\subseteq[n]$, put $Z_S=\prod_{i\in S}Z_i$. For an integer $M\ge2$ put $\epsilon=\beta/M$; the layer $k$ satisfies $1\le k<M$. All Trotter quantities are computed from the ordered product $L=\prod_{ij}e^{-\epsilon H_{ij}/2}$ and the cyclic trace polynomial. If $\epsilon\Gamma\le1/2$ and $48(\beta\Gamma^2+W)\epsilon\le1$, then the exact and Trotter one- and two-insertion moments of Eqs. (78)–(79) satisfy both bounds
--   $$|G_2(k\epsilon)-G_{2,\epsilon}(k)|\le16(\beta\Gamma^2+W)\epsilon,\qquad |G_1-G_{1,\epsilon}|\le16(\beta\Gamma^2+W)\epsilon.$$
--   These two quantitative comparisons have a shared error constant and retain both clauses of the source.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Lemma 17, printed/PDF p. 20

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem moment_comparison {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (h : ℝ) (hh : 0 < h) (β : ℝ) (hβ : 0 < β) (S : Finset (Fin n)) (hS : S.Nonempty) (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (hk : 1 ≤ k) (hkM : k < M)
    (hε : stepSize β M * gamma B h ≤ 1/2)
    (hCT : cT B h β * stepSize β M ≤ 1) :
    ‖twoPoint (fieldHamiltonian B h) (zProduct S) (zProduct S) β (k * stepSize β M) -
      trotterMomentTwo B h β M S k‖ ≤ 16 * (β * (gamma B h)^2 + weight B) * stepSize β M ∧
    ‖mean (fieldHamiltonian B h) (zProduct S) β - trotterMomentOne B h β M S‖ ≤
      16 * (β * (gamma B h)^2 + weight B) * stepSize β M := by sorry
end LeeYangGap.SpectralGap
