-- Prove2me | Theorems.Thm_MultiSecretary_BR_state_space_reduction
-- name    : MultiSecretary.BR.state_space_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:58:10.980579+00:00
-- url     : https://prove2.me/theorems/d48565b1-91e9-4c15-8ea9-8a558cfa8eb7
-- title:
--   Proposition 5 — state-space reduction (49): $v_\ell(w,\kappa)=w+g_\ell(\kappa)$
-- statement:
--   In the multi-secretary model, let $v_\ell(w,\kappa)$, for $\ell\ge0$ periods to go, accrued ability $w\ge0$ and residual budget $\kappa\in\mathbb Z_+$, satisfy the Bellman recursion
--   $$v_\ell(w,\kappa)=\sum_{j\in[m]}\max\{v_{\ell-1}(w+a_j,\kappa-1),\,v_{\ell-1}(w,\kappa)\}f_j\tag{46}$$
--   with $v_0(w,\kappa)=w$ and $v_\ell(w,0)=w$. Let $g_\ell:\mathbb Z_+\to\mathbb R_+$ satisfy
--   $$g_\ell(\kappa)=\sum_{j\in[m]}\max\{a_j+g_{\ell-1}(\kappa-1),\,g_{\ell-1}(\kappa)\}f_j\tag{47}$$
--   with $g_0(\kappa)=0$ and $g_\ell(0)=0$ for $\ell\ge1$ (48). Then
--   $$v_\ell(w,\kappa)=w+g_\ell(\kappa)\qquad\text{for all }w\ge0,\ \kappa\in\mathbb Z_+.\tag{49}$$
--
--   The optimal continuation value does not depend on the accrued ability, so optimal thresholds depend only on the remaining time and budget.
--
--   **Formalization Note** The recursions (46) and (47) are imposed for $\ell\ge1$ and $\kappa\ge1$; at $\kappa=0$ the boundary conditions apply (the printed recursion would refer to $\kappa-1=-1$). Only identity (49) is formalized; the proposition's "Consequently" sentence (optimality of the threshold rule $a_j\ge h_\ell(\kappa)$) needs the dynamic-programming principle $V^*_{\mathrm{on}}(n,k)=v_n(0,k)$ and is not part of this item.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Proposition 5, Appendix C, p. 39, eqs. (46)–(49) ((46) on p. 38)

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model

namespace MultiSecretary.BR

/-- Proposition 5 (State-space Reduction), Appendix C, p. 39, identity (49). Let `v_ℓ(w, κ)`
satisfy the Bellman recursion (46), p. 38,
`v_ℓ(w, κ) = ∑_j max{v_{ℓ−1}(w + a_j, κ − 1), v_{ℓ−1}(w, κ)} f_j`, with `v_0(w, κ) = w` and
`v_ℓ(w, 0) = w`, and let `g_ℓ : ℤ₊ → ℝ₊` satisfy (47)
`g_ℓ(κ) = ∑_j max{a_j + g_{ℓ−1}(κ − 1), g_{ℓ−1}(κ)} f_j` with the boundary conditions (48)
`g_0(κ) = 0`, `g_ℓ(0) = 0` (`ℓ ≥ 1`). Then `v_ℓ(w, κ) = w + g_ℓ(κ)` for all `w ≥ 0` and `κ`.
The recursions are imposed for `ℓ ≥ 1`, `κ ≥ 1`, `w ≥ 0`; at `κ = 0` the boundary conditions apply. -/
theorem state_space_reduction {m : ℕ} (I : Instance m) (v : ℕ → ℝ → ℕ → ℝ) (g : ℕ → ℕ → ℝ)
    (hv : ∀ ℓ κ w, 1 ≤ ℓ → 1 ≤ κ → 0 ≤ w →
      v ℓ w κ = ∑ j, max (v (ℓ - 1) (w + I.a j) (κ - 1)) (v (ℓ - 1) w κ) * I.f j)
    (hv0 : ∀ κ w, 0 ≤ w → v 0 w κ = w)
    (hvκ : ∀ ℓ w, 1 ≤ ℓ → 0 ≤ w → v ℓ w 0 = w)
    (hg_nonneg : ∀ ℓ κ, 0 ≤ g ℓ κ)
    (hg : ∀ ℓ κ, 1 ≤ ℓ → 1 ≤ κ →
      g ℓ κ = ∑ j, max (I.a j + g (ℓ - 1) (κ - 1)) (g (ℓ - 1) κ) * I.f j)
    (hg0 : ∀ κ, g 0 κ = 0)
    (hgκ : ∀ ℓ, 1 ≤ ℓ → g ℓ 0 = 0) :
    ∀ ℓ κ w, 0 ≤ w → v ℓ w κ = w + g ℓ κ := by sorry

end MultiSecretary.BR
