-- Prove2me | Theorems.Thm_NonstatRL_NoWidening_visited_average_reaches
-- name    : NonstatRL.NoWidening.visited_average_reaches
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:50.105132+00:00
-- url     : https://prove2.me/theorems/49628189-185e-45af-a466-f61f1020b3eb
-- title:
--   Proof of Lemma 13, second case — visited transition averages retain one-step reachability
-- statement:
--   Suppose the state space has at least two states, every state has an allowed action, the confidence level lies in $0<\delta<1$, and a fixed allowed action $a_{(s,s')}$ sends state $s$ to state $s'$ with probability at least $\zeta>0$ at every time up to the horizon. If $(s,a_{(s,s')})$ has been visited in the window for time $t$, then its average true transition probability satisfies
--
--   $$\bar p_t(s'\mid s,a_{(s,s')})\ge\zeta.$$
--
--   On the event $E_p$, the entire averaged row $\bar p_t(\cdot\mid s,a_{(s,s')})$ belongs to the unwidened confidence region. These are the two claims in the visited-pair case of Lemma 13.
--
--   **Formalization Note** Times are zero-based, with $\tau_m\le t<T$ and window `[τm-W,t)`. The one-time event $E_p$ uses only the $\ell_1$ condition; positive visit count makes the averaged row a probability distribution. Assumption 2 quantifies over all times $q<T$.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 50, proof of Lemma 13, second case

import Mathlib
import Definitions.Def_NonstatRL_PerStep_Window

open BanditAlgorithm

namespace NonstatRL.NoWidening

theorem visited_average_reaches {S A : ℕ} (hS : 1 < S)
    (M : ℕ → FiniteMDP S A) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (W τm t : ℕ)
    (hτ : τm ≤ t) (ht : t < T)
    (ζ : ℝ) (hζ : 0 < ζ) (a₂ : Fin S → Fin S → Fin A)
    (ha₂ : ∀ s s', a₂ s s' ∈ As s)
    (hreach : ∀ q < T, ∀ s s', ζ ≤ ((M q).P s (a₂ s s') s' : ℝ))
    (hEp : NonstatRL.PerStep.EventP M As T δ st ac (τm - W) t) :
    ∀ s s', 0 < NonstatRL.PerStep.count st ac (τm - W) t s (a₂ s s') →
      ζ ≤ NonstatRL.PerStep.pBar M st ac (τm - W) t s (a₂ s s') s' ∧
      (fun y => NonstatRL.PerStep.pBar M st ac (τm - W) t s (a₂ s s') y) ∈
        NonstatRL.PerStep.Hp As T δ st ac (τm - W) t 0 s (a₂ s s') := by sorry

end NonstatRL.NoWidening
