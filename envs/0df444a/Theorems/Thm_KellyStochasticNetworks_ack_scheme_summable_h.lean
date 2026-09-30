-- Prove2me | Theorems.Thm_KellyStochasticNetworks_ack_scheme_summable_h
-- name    : KellyStochasticNetworks.ack_scheme_summable_h
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:13:07.538476+00:00
-- url     : https://prove2.me/theorems/1d02df60-dbde-425e-9797-3d262252154a
-- title:
--   Exercise 5.8 — a scheme that gives up has $\nu_c = \infty$
-- statement:
--   Consider an acknowledgement-based scheme whose retransmission function is non-negative and
--   **summable**, $\sum_{x\ge1}h(x)<\infty$. By the first Borel–Cantelli lemma a packet then makes
--   only finitely many attempts — the scheme discards it after finitely many tries. Show that its
--   critical rate is infinite: for every arrival rate $\nu>0$,
--   $$H(\nu)=\sum_{t\ge1}P_t=\infty .$$
--
--   The reason is immediate once stated: if $S_t=\sum_{r\le t}h(r)$ converges to a finite limit
--   $S_\infty$, then $P_t=(1+\nu S_t)e^{-\nu S_t}$ converges to $(1+\nu S_\infty)e^{-\nu
--   S_\infty}>0$, and a series whose terms do not tend to zero diverges.
--
--   This is the opposite extreme from the goal of this mission. A scheme that retransmits
--   persistently enough to satisfy condition (5.7) jams at every positive rate; a scheme that gives
--   up entirely has $H(\nu)$ infinite at every positive rate, so infinitely many slots stay
--   uncontested — at the cost of the packets it discarded. Between them lie the schemes with a
--   finite positive $\nu_c$, of which Ethernet is one.
--
--   **Formalization Note** "$H(\nu)=\infty$" is stated as failure of summability of the sequence
--   of slot probabilities, which is the form the argument produces and the form the definition of
--   $\nu_c$ uses.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 125 (PDF p. 133), Exercise 5.8: 'Show that if sum_{x=1}^{infinity} h(x) < infinity a packet is transmitted at most a finite number of times (equivalently, it is discarded after a finite number of attempts), and that nu_c = infinity. [Hint: First Borel-Cantelli lemma.]' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem ack_scheme_summable_h (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x) (hsum : Summable h)
    (ν : ℝ) (hν : 0 < ν) : ¬ Summable (fun t : ℕ => ackSlotProb h ν (t + 1)) := by sorry

end KellyStochasticNetworks
