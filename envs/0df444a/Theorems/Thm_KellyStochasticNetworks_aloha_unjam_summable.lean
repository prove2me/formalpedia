-- Prove2me | Theorems.Thm_KellyStochasticNetworks_aloha_unjam_summable
-- name    : KellyStochasticNetworks.aloha_unjam_summable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:11:29.749974+00:00
-- url     : https://prove2.me/theorems/52506ca8-bd7b-42d1-86cc-f605b21734cb
-- title:
--   Proposition 5.3 (proof) — the unjamming probabilities are summable
-- statement:
--   Fix an arrival rate $\nu > 0$ and a retransmission probability $f \in (0,1)$, and let $p(n)$ be
--   the probability that the ALOHA channel unjams before the backlog increases, starting from
--   backlog $n$:
--   $$p(n)=\frac{e^{-\nu}(1+\nu)(1-f)^{n}+e^{-\nu}nf(1-f)^{n-1}}
--               {1-e^{-\nu}\bigl(1-(1-f)^{n}-nf(1-f)^{n-1}\bigr)} .$$
--   Then $\sum_{n \ge 0} p(n) < \infty$.
--
--   This is the step that makes Proposition 5.3 work. Summability plus the first Borel–Cantelli
--   lemma gives that only finitely many of the unjamming events occur, so with probability one
--   there is a finite time after which every slot is a collision: ALOHA transmits finitely many
--   packets and then jams forever, at every positive arrival rate.
--
--   The mechanism is that the numerator decays geometrically, like $nf(1-f)^{n-1}$, while the
--   denominator stays bounded away from zero — it is at least $1-e^{-\nu}$, because the quantity
--   subtracted from $1$ is $e^{-\nu}$ times a probability. So $p(n) \sim
--   nf(1-f)^{n-1}/(e^{\nu}-1)$, which is summable.
--
--   **Formalization Note** Summability is asserted rather than a value for the sum, which is what
--   the Borel–Cantelli step needs. The denominator is never zero under the stated hypotheses, so
--   the quotient is the intended one at every $n$ rather than a junk value at some.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 111 (PDF p. 119), in the proof of Proposition 5.3: 'p(n) = P(Z_t = 0 or 1 | N_t = n) / (1 - P(N_{t+1} = n, Z_t = * | N_t = n)) = (e^{-nu}(1+nu)(1-f)^n + e^{-nu} n f (1-f)^{n-1}) / (1 - e^{-nu}(1 - (1-f)^n - n f (1-f)^{n-1})) ~ n f (1-f)^{n-1}/(e^{nu} - 1) as n -> infinity. As we expected, p(n) -> 0 as n -> infinity. Moreover, they are summable: sum_{n=0}^{infinity} p(n) < infinity. Summable sequences of probabilities bring to mind the first Borel-Cantelli lemma.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem aloha_unjam_summable (ν f : ℝ) (hν : 0 < ν) (hf : 0 < f) (hf1 : f < 1) :
    Summable (alohaUnjamProb ν f) := by sorry

end KellyStochasticNetworks
