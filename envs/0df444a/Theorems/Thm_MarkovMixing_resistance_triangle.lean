-- Prove2me | Theorems.Thm_MarkovMixing_resistance_triangle
-- name    : MarkovMixing.resistance_triangle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:01:15.811564+00:00
-- url     : https://prove2.me/theorems/014d336c-9ebb-4627-844d-c745fb601c02
-- title:
--   Corollary 10.8 -- the resistance triangle inequality
-- statement:
--   Let $c$ be a **network** on a finite vertex set: a symmetric nonnegative conductance function with total conductance $c(x)=\sum_yc(x,y)>0$ at every vertex, whose associated walk $P(x,y)=c(x,y)/c(x)$ is irreducible. For distinct vertices, the **effective resistance** $R(a\leftrightarrow z)$ is defined through the voltage $W(x)=\mathbb P_x\{\tau_a<\tau_z\}$ and the current $\|I\|=\sum_yc(a,y)[W(a)-W(y)]$ as $R(a\leftrightarrow z)=\|I\|^{-1}$.
--
--   The theorem (Corollary 10.8 of Levin–Peres–Wilmer) asserts that effective resistance satisfies the triangle inequality: for pairwise distinct vertices $a,b,z$,
--   $$R(a\leftrightarrow z)\;\le\;R(a\leftrightarrow b)+R(b\leftrightarrow z).$$
--   Together with symmetry and positivity this makes $R$ a genuine metric on the vertices of a connected network — the *resistance metric*. In the book it is a direct consequence of the commute time identity, which converts the claim into the sub-additivity of round-trip times through the intermediate vertex $b$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 10.3, Corollary 10.8, Eq. (10.10), p. 131

import Definitions.Def_mm_network

namespace MarkovMixing

/-- **Corollary 10.8** (LPW): effective resistance satisfies the triangle
inequality `R(a↔c) ≤ R(a↔b) + R(b↔c)`. -/
theorem resistance_triangle {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hc : IsConductance c)
    (hpos : ∀ x : V, 0 < vertexConductance c x)
    (hirr : Irreducible (networkWalk c)) (a b z : V)
    (hab : a ≠ b) (hbz : b ≠ z) (haz : a ≠ z) :
    effectiveResistance c a z ≤
      effectiveResistance c a b + effectiveResistance c b z := by
  sorry

end MarkovMixing
