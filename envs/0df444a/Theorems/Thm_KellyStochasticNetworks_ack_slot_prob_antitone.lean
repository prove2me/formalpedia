-- Prove2me | Theorems.Thm_KellyStochasticNetworks_ack_slot_prob_antitone
-- name    : KellyStochasticNetworks.ack_slot_prob_antitone
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:12:35.747588+00:00
-- url     : https://prove2.me/theorems/20100f17-9241-4b0b-ac90-3026ef081212
-- title:
--   Section 5.3 — the slot probabilities decrease in the arrival rate
-- statement:
--   For an acknowledgement-based scheme with non-negative retransmission function $h$, the
--   probability that fewer than two attempts are made in slot $t$ of the externally jammed
--   channel,
--   $$P_t(\nu)=\Bigl(1+\nu S_t\Bigr)e^{-\nu S_t}, \qquad S_t=\sum_{r=1}^{t}h(r),$$
--   is a decreasing function of the arrival rate $\nu$ on $[0,\infty)$.
--
--   This is the observation that makes the critical rate $\nu_c=\inf\{\nu : H(\nu)<\infty\}$ a
--   genuine threshold rather than an arbitrary infimum: since every $P_t$ decreases in $\nu$, so
--   does $H(\nu)=\sum_t P_t$, and the set $\{\nu : H(\nu)<\infty\}$ is therefore an up-set. Without
--   it, "$H$ is finite above $\nu_c$ and infinite below" would not follow from the definition of
--   $\nu_c$.
--
--   The derivative is $-\nu S_t^2 e^{-\nu S_t}$, which is where the monotonicity comes from: the
--   growth of the linear factor is dominated by the exponential decay for every $\nu>0$.
--
--   **Formalization Note** "Decreasing" is in the weak sense, which is what holds at $S_t=0$ —
--   that is, at $t=0$, or for a scheme that never transmits — where $P_t$ is identically $1$.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 120 (PDF p. 128), section 5.3: 'The probabilities P_t, and hence H(nu), are decreasing in nu. Let nu_c = inf{nu : H(nu) < infinity}.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem ack_slot_prob_antitone (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x) (t : ℕ) :
    AntitoneOn (fun ν : ℝ => ackSlotProb h ν t) (Set.Ici 0) := by sorry

end KellyStochasticNetworks
