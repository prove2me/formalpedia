-- Prove2me | Theorems.Thm_MarkovMixing_green_resistance
-- name    : MarkovMixing.green_resistance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:00:07.756698+00:00
-- url     : https://prove2.me/theorems/2f8057ea-ef67-4707-8183-66fa6ce02671
-- title:
--   Lemma 9.6 -- the Green's function and effective resistance
-- statement:
--   Let $c$ be a **network** on a finite vertex set: a symmetric nonnegative conductance function with total conductance $c(x)=\sum_yc(x,y)>0$ at every vertex, carrying the walk $P(x,y)=c(x,y)/c(x)$, assumed irreducible. Fix distinct vertices $a\ne z$. The **Green's function** of the walk stopped at $z$ is the expected number of visits to a vertex before first hitting $z$:
--   $$G_{\tau_z}(a,x)=\mathbb E_a\bigl[\#\{t<\tau_z: X_t=x\}\bigr],$$
--   the walk starting at $a$ and $\tau_z$ being the hitting time of $z$. The **effective resistance** $R(a\leftrightarrow z)$ is defined through the voltage: with $W(x)=\mathbb P_x\{\tau_a<\tau_z\}$ (the harmonic function with boundary values $W(a)=1$, $W(z)=0$), the current flowing out of $a$ is $\|I\|=\sum_yc(a,y)\bigl[W(a)-W(y)\bigr]$, and $R(a\leftrightarrow z)=\|I\|^{-1}$.
--
--   The theorem (Lemma 9.6 of Levin–Peres–Wilmer) asserts:
--   $$G_{\tau_z}(a,a)\;=\;c(a)\,R(a\leftrightarrow z).$$
--   The expected number of returns to the starting point before reaching $z$ is exactly the vertex conductance times the effective resistance — the identity through which escape probabilities and resistances translate into each other.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 9.4, Lemma 9.6, Eq. (9.18), p. 120

import Definitions.Def_mm_network

namespace MarkovMixing

/-- **Lemma 9.6** (LPW): the Green's function of the network walk stopped at
`τ_z` satisfies `G_{τ_z}(a,a) = c(a) R(a ↔ z)`. -/
theorem green_resistance {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hc : IsConductance c)
    (hpos : ∀ x : V, 0 < vertexConductance c x)
    (hirr : Irreducible (networkWalk c)) (a z : V) (haz : a ≠ z) :
    greenFn (networkWalk c) a z a =
      vertexConductance c a * effectiveResistance c a z := by
  sorry

end MarkovMixing
