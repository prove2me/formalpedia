-- Prove2me | Theorems.Thm_MarkovMixing_commute_time_identity
-- name    : MarkovMixing.commute_time_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:01:02.42094+00:00
-- url     : https://prove2.me/theorems/096e6c68-bde8-45b8-8558-b1f544449833
-- title:
--   Proposition 10.6 -- the commute time identity
-- statement:
--   Let $c$ be a **network** on a finite vertex set $V$: a symmetric nonnegative conductance function with total vertex conductance $c(x)=\sum_yc(x,y)>0$ everywhere, carrying the irreducible walk $P(x,y)=c(x,y)/c(x)$. Write $c_G=\sum_xc(x)$ for the total conductance of the network, $\mathbb E_a(\tau_b)$ for the expected number of steps for the walk started at $a$ to first reach $b$, and $R(a\leftrightarrow b)$ for the **effective resistance**, defined through the voltage $W(x)=\mathbb P_x\{\tau_a<\tau_b\}$ and current $\|I\|=\sum_yc(a,y)[W(a)-W(y)]$ as $R(a\leftrightarrow b)=\|I\|^{-1}$.
--
--   The theorem (the **Commute Time Identity**, Proposition 10.6 of Levin–Peres–Wilmer, the capstone of Chapters 9–11) asserts: for any two distinct vertices $a\ne b$,
--   $$\mathbb E_a(\tau_b)+\mathbb E_b(\tau_a)\;=\;c_G\;R(a\leftrightarrow b).$$
--   The expected round-trip time between two vertices is exactly the total conductance times the effective resistance between them. This single identity converts the entire electrical toolkit — series/parallel reduction, Thomson's principle, Rayleigh monotonicity — into exact computations and bounds for hitting and cover times of reversible chains.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 10.3, Proposition 10.6, Eq. (10.8), p. 130

import Definitions.Def_mm_network

namespace MarkovMixing

/-- **Proposition 10.6, the Commute Time Identity** (LPW), the capstone of
Chapters 9–11: for the random walk on a network,
`E_a(τ_b) + E_b(τ_a) = c_G · R(a ↔ b)`. -/
theorem commute_time_identity {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hc : IsConductance c)
    (hpos : ∀ x : V, 0 < vertexConductance c x)
    (hirr : Irreducible (networkWalk c)) (a b : V) (hab : a ≠ b) :
    expSetHitTime (networkWalk c) a {b} + expSetHitTime (networkWalk c) b {a} =
      totalConductance c * effectiveResistance c a b := by
  sorry

end MarkovMixing
