-- Prove2me | Theorems.Thm_KellyStochasticNetworks_aloha_attempt_rate
-- name    : KellyStochasticNetworks.aloha_attempt_rate
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:13:33.833038+00:00
-- url     : https://prove2.me/theorems/5d0f7ff3-5a64-4c8d-961d-3e0574dc800e
-- title:
--   Example 5.8 — ALOHA satisfies condition (5.7)
-- statement:
--   The ALOHA protocol is the acknowledgement-based scheme with $h(1)=1$ and $h(x)=f$ for every
--   $x>1$, where $f\in(0,1)$ is the retransmission probability. Two facts.
--
--   1. Its attempt-rate partial sums are exactly linear:
--      $$\sum_{r=1}^{t+1}h(r)=1+tf \qquad\text{for every } t\ge 0 .$$
--   2. Consequently it satisfies condition (5.7):
--      $$\frac{1}{\log t}\sum_{x=1}^{t}h(x)\longrightarrow\infty \qquad (t\to\infty).$$
--
--   Linear growth is much faster than logarithmic, so ALOHA is at the far end of the range the
--   condition covers. Combined with the goal of this mission, it gives $\nu_c=0$ for ALOHA, which
--   is the analytic counterpart of Proposition 5.3: whatever the arrival rate, the channel
--   eventually jams. The contrast to hold in mind is Ethernet's binary exponential backoff, where
--   $\sum_{r\le t}h(r)\sim\log_2 t$ grows at exactly the critical rate and produces
--   $\nu_c=\log 2$.
--
--   **Formalization Note** The first identity is stated at $t+1$ so that the sum is over a
--   non-empty range of slots and no index has to be decremented. The quotient in the second is not
--   meaningful at $t=0,1$, where $\log t\le0$; divergence is an eventual statement, so this is
--   immaterial.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 120 (PDF p. 128), Example 5.8: 'For the ALOHA protocol of Section 5.1, h(x) = f for all x > 1.' And p. 123 (PDF p. 131), condition (5.7): 'nu_c = 0 whenever (log t)^{-1} sum_{x=1}^{t} h(x) -> infinity as t -> infinity.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem aloha_attempt_rate (f : ℝ) (hf : 0 < f) :
    (∀ t : ℕ, ackAttemptRate (alohaH f) (t + 1) = 1 + (t : ℝ) * f)
      ∧ Filter.Tendsto (fun t : ℕ => ackAttemptRate (alohaH f) t / Real.log t)
          Filter.atTop Filter.atTop := by sorry

end KellyStochasticNetworks
