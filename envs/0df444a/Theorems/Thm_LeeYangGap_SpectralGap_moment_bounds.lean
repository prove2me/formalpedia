-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_moment_bounds
-- name    : LeeYangGap.SpectralGap.moment_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:17.759188+00:00
-- url     : https://prove2.me/theorems/8f1cfc6c-6ebb-4815-99bd-c3bcaf81e15c
-- title:
--   Lemma 16 — Moment bounds
-- statement:
--   Let $H$ be a Lee–Yang Hamiltonian on $n\ge1$ qubits, with all five real bond coefficients satisfying Definition 1, and let $H_h=H-h\sum_iZ_i$ for $h>0$. Let $\beta>0$, $W=\sum_{ij}w^z_{ij}$ and $\Gamma=3W+nh$. For every nonempty site subset $S$, every real $t\in[0,\beta]$, every integer $M\ge1$ and every interior layer $1\le k<M$, the exact moments $G_1=\langle Z_S\rangle_\beta$, $G_2(t)=\langle Z_S(0)Z_S(t)\rangle_\beta$ and the computed Trotter moments of Eq. (78) obey
--   $$|G_1|\le1,\quad |G_2(t)|\le1,\quad |G_{1,\epsilon}|\le1,\quad |G_{2,\epsilon}(k)|\le1.$$
--   No small-step assumption is required. The one-insertion estimate also includes $M=1$, when there is no interior layer. These bounds compare moments in the same normalization as the connected correlators.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Lemma 16, printed/PDF p. 20

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem moment_bounds {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (h : ℝ) (hh : 0 < h) (β : ℝ) (hβ : 0 < β) (S : Finset (Fin n)) (hS : S.Nonempty) (M : ℕ) (hM : 1 ≤ M) :
    ‖mean (fieldHamiltonian B h) (zProduct S) β‖ ≤ 1 ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ β →
      ‖twoPoint (fieldHamiltonian B h) (zProduct S) (zProduct S) β t‖ ≤ 1) ∧
    ‖trotterMomentOne B h β M S‖ ≤ 1 ∧
    (∀ k : ℕ, 1 ≤ k → k < M → ‖trotterMomentTwo B h β M S k‖ ≤ 1) := by sorry
end LeeYangGap.SpectralGap
