-- Prove2me | Theorems.Thm_NonstatRL_NoWidening_proposition4_diameter_le_inv_zeta
-- name    : NonstatRL.NoWidening.proposition4_diameter_le_inv_zeta
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:08.836216+00:00
-- url     : https://prove2.me/theorems/9860b5a6-4da2-4ccf-969d-208b4848b0f9
-- title:
--   Proposition 4 — the unwidened region contains an MDP of diameter at most 1/ζ
-- statement:
--   Consider a nonstationary finite MDP with at least two states and a nonempty allowed action set at each state. Assume uniform one-step reachability: for every ordered pair of states $(s,s')$, a fixed allowed action $a_{(s,s')}$ moves from $s$ to $s'$ with probability at least $\zeta>0$ at every time before the horizon. Let $0<\delta<1$, and condition on the transition estimation event $E_p$ at any time $t$ in an episode with start $\tau_m\le t$.
--
--   There exists a finite MDP $M_w$ such that all its allowed transition rows lie in the unwidened confidence region $H_{p,t}(0)$ and
--
--   $$D(M_w)\le\frac1\zeta.$$
--
--   The proposition shows that, under Assumption 2, the algorithm's transition region already contains a model with a controlled diameter without confidence widening.
--
--   **Formalization Note** Paper time $t\in[T]$ is Lean index $t-1<T$; the window is `[τm-W,t)` in zero-based indices. The event is the $\ell_1$ estimation condition at this time. The diameter includes return times and minimizes over allowed deterministic stationary policies. The pins $S>1$ and $0<\delta<1$ exclude a small-state radius failure; the constructed MDP must satisfy the region condition at every allowed pair. Disallowed rows and rewards are irrelevant.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 21, Proposition 4; proof pp. 49–50

import Mathlib
import Definitions.Def_NonstatRL_PerStep_Window

open BanditAlgorithm

namespace NonstatRL.NoWidening

theorem proposition4_diameter_le_inv_zeta {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (W τm t : ℕ)
    (hτ : τm ≤ t) (ht : t < T)
    (ζ : ℝ) (hζ : 0 < ζ) (a₂ : Fin S → Fin S → Fin A)
    (ha₂ : ∀ s s', a₂ s s' ∈ As s)
    (hreach : ∀ q < T, ∀ s s', ζ ≤ ((M q).P s (a₂ s s') s' : ℝ))
    (hEp : NonstatRL.PerStep.EventP M As T δ st ac (τm - W) t) :
    ∃ Mw : FiniteMDP S A,
      (∀ s, ∀ a ∈ As s,
        (fun s' => (Mw.P s a s' : ℝ)) ∈ NonstatRL.PerStep.Hp As T δ st ac (τm - W) t 0 s a) ∧
      NonstatRL.Oracle.diameter Mw As ≤ ENNReal.ofReal (1 / ζ) := by sorry

end NonstatRL.NoWidening
