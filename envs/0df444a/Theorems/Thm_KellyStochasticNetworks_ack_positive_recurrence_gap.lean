-- Prove2me | Theorems.Thm_KellyStochasticNetworks_ack_positive_recurrence_gap
-- name    : KellyStochasticNetworks.ack_positive_recurrence_gap
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:13:59.416728+00:00
-- url     : https://prove2.me/theorems/cec24895-aaaa-4a53-b79a-ed215d912778
-- title:
--   Remark 5.14 — positive recurrence needs $\nu \le e^{-\nu}$, strictly below $\log 2$
-- statement:
--   A balance argument bounds the arrival rate at which an acknowledgement-based scheme can be
--   positive recurrent. In equilibrium the expected number of packets transmitted per slot must
--   equal the expected number arriving, and the former is at most $e^{-\nu}$, so a positive
--   recurrent system requires
--   $$\nu \le e^{-\nu}.$$
--   Two consequences are asserted.
--
--   1. Any $\nu>0$ with $\nu\le e^{-\nu}$ satisfies $\nu<0.5672$. (The exact threshold is the
--      solution of $\nu=e^{-\nu}$, the omega constant $\Omega\approx 0.5671433$.)
--   2. $0.5672<\log 2$.
--
--   Together these say that the interval $(0.5672,\ \log 2)$ is non-empty and that on it an
--   acknowledgement-based scheme cannot be positive recurrent — even though Ethernet, whose
--   critical rate is $\nu_c=\log 2$, does transmit infinitely many packets there. "Infinitely many
--   packets get through" is strictly weaker than "the backlog is stable", and this is the gap
--   between them.
--
--   **Formalization Note** The balance argument that produces the hypothesis $\nu\le e^{-\nu}$ is
--   a statement about an equilibrium distribution of the backlog chain and is not formalized here;
--   what is asserted is the numerical consequence drawn from it, together with the comparison
--   against $\log 2$ that makes the gap non-empty.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 123 (PDF p. 131), Remark 5.14: 'suppose we had a positive recurrent system, with pi_0 the equilibrium probability of 0 retransmissions, and pi_1 the equilibrium probability of 1 retransmission in any given time slot. Then the expected number of (new and old) packet transmissions in a slot is pi_1 e^{-nu} + pi_0 nu e^{-nu}, while the expected number of arrivals is nu. Now, pi_0 + pi_1 <= 1, and clearly nu <= 1, so pi_1 e^{-nu} + pi_0 nu e^{-nu} <= e^{-nu}, and we obtain nu <= e^{-nu} => nu <= 0.567. Thus, for 0.567 < nu < 0.693, an acknowledgement-based scheme is most definitely not positive recurrent, even though Ethernet will have an infinite number of packets successfully transmitted in this range.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem ack_positive_recurrence_gap :
    (∀ ν : ℝ, 0 < ν → ν ≤ Real.exp (-ν) → ν < 0.5672)
      ∧ (0.5672 : ℝ) < Real.log 2 := by sorry

end KellyStochasticNetworks
