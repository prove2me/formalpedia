-- Prove2me | Theorems.Thm_NonstatRL_NoWidening_lemma13_region_contains_reaching_mdp
-- name    : NonstatRL.NoWidening.lemma13_region_contains_reaching_mdp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:56.02198+00:00
-- url     : https://prove2.me/theorems/0c506386-a454-4138-bcea-b231ea6e4708
-- title:
--   Lemma 13 — a transition model in the unwidened region retains one-step reachability
-- statement:
--   Let a nonstationary finite MDP have at least two states and a nonempty allowed action set at every state. Suppose $0<\delta<1$ and Assumption 2 holds: there is $\zeta>0$ and, for each pair $(s,s')$, an allowed action $a_{(s,s')}$ whose probability of moving from $s$ to $s'$ is at least $\zeta$ at every time. Condition on the transition estimation event $E_p$ at a time $t<T$ in an episode beginning at $\tau_m\le t$.
--
--   There is a finite MDP with transition law $p$ whose every allowed row is in the unwidened confidence region and which satisfies
--
--   $$p(s'\mid s,a_{(s,s')})\ge\zeta\qquad\text{for all states }s,s'.$$
--
--   The lemma provides a single admissible transition model, covering visited and unvisited pairs together.
--
--   **Formalization Note** The window is `[τm-W,t)` under zero-based time. Assumption 2 holds for every index $q<T$, including the current time; the event is required only at the selected time. The constructed MDP's rewards and disallowed-action rows are arbitrary. The pins $S>1$ and $0<\delta<1$ make the printed unvisited-pair radius claim valid.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 49, Lemma 13; proof p. 50

import Mathlib
import Definitions.Def_NonstatRL_PerStep_Window

open BanditAlgorithm

namespace NonstatRL.NoWidening

theorem lemma13_region_contains_reaching_mdp {S A : ℕ} (hS : 1 < S)
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
      ∀ s s', ζ ≤ (Mw.P s (a₂ s s') s' : ℝ) := by sorry

end NonstatRL.NoWidening
