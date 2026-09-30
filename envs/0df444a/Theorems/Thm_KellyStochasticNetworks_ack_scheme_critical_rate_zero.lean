-- Prove2me | Theorems.Thm_KellyStochasticNetworks_ack_scheme_critical_rate_zero
-- name    : KellyStochasticNetworks.ack_scheme_critical_rate_zero
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:14:32.223662+00:00
-- url     : https://prove2.me/theorems/22376dc6-0533-4b71-8468-870e49d6e0a7
-- title:
--   Condition (5.7) — slower-than-exponential backoff has critical rate zero
-- statement:
--   Consider an acknowledgement-based random access scheme with non-negative retransmission
--   function $h$, and let
--   $$P_t=\Bigl(1+\nu\sum_{r=1}^{t}h(r)\Bigr)\exp\Bigl(-\nu\sum_{r=1}^{t}h(r)\Bigr)$$
--   be the probability that fewer than two attempts are made in slot $t$ of the externally jammed
--   channel. Suppose the scheme backs off more slowly than exponentially, in the sense of the
--   book's condition (5.7):
--   $$\frac{1}{\log t}\sum_{x=1}^{t}h(x)\longrightarrow\infty \qquad (t\to\infty).$$
--   Then for **every** arrival rate $\nu>0$ the series $\sum_{t\ge1}P_t$ converges.
--
--   Since $H(\nu)=\sum_t P_t$ is finite for every positive $\nu$, the critical rate
--   $\nu_c=\inf\{\nu : H(\nu)<\infty\}$ is zero. By Theorem 5.11 that means the expected number of
--   successful transmissions is finite at every positive arrival rate: the channel jams. In the
--   book's words, this holds "for any acknowledgement-based scheme with slower than exponential
--   backoff".
--
--   The threshold is sharp in the sense that matters for protocol design. A fixed retransmission
--   probability, as in ALOHA, gives $\sum_{x\le t}h(x)$ growing linearly and so falls under this
--   result; Ethernet's binary exponential backoff gives growth like $\log_2 t$, exactly at the
--   boundary, and has the positive critical rate $\nu_c=\log 2$. Exponential backoff is not a
--   tuning choice but the minimum that makes a contention protocol work at all.
--
--   **Formalization Note** The conclusion is stated as summability of the sequence of slot
--   probabilities at each fixed $\nu>0$, which is what "$H(\nu)<\infty$" means and what the
--   definition of $\nu_c$ consumes; it is not stated as a claim about the infimum, which adds
--   nothing once the set of such $\nu$ is known to be all of $(0,\infty)$. The hypothesis is
--   condition (5.7) verbatim, as a limit; the quotient is not meaningful at $t=0,1$, where
--   $\log t\le0$, and divergence being eventual makes that immaterial. Beyond non-negativity no
--   regularity of $h$ is assumed.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 123 (PDF p. 131), condition (5.7): 'More generally, nu_c = 0 whenever (log t)^{-1} sum_{x=1}^{t} h(x) -> infinity as t -> infinity, (5.7) since this implies sum_{t=1}^{infinity} P_t < infinity for any nu > 0 (Exercise 5.8). In this sense, the expected number of successful transmissions is finite for any acknowledgement-based scheme with slower than exponential backoff.' With P_t from p. 120. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem ack_scheme_critical_rate_zero (h : ℕ → ℝ) (hh : ∀ x, 0 ≤ h x)
    (hgrow : Filter.Tendsto (fun t : ℕ => ackAttemptRate h t / Real.log t)
        Filter.atTop Filter.atTop)
    (ν : ℝ) (hν : 0 < ν) :
    Summable (fun t : ℕ => ackSlotProb h ν (t + 1)) := by sorry

end KellyStochasticNetworks
