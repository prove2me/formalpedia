-- Prove2me | Theorems.Thm_MarkovMixing_harmonic_eq_const
-- name    : MarkovMixing.harmonic_eq_const
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:42:20.341352+00:00
-- url     : https://prove2.me/theorems/692c0b1c-3b9e-456d-8ebb-b10b0b06bc07
-- title:
--   Lemma 1.16 -- harmonic functions of an irreducible chain are constant
-- statement:
--   If $P$ is stochastic and irreducible and $h:V\to\mathbb{R}$ satisfies $h(x)=\sum_y P(x,y)h(y)$ at every state $x$ (i.e. $h$ is harmonic everywhere), then $h$ is constant: $h(x)=h(y)$ for all $x,y$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 1.5.4, Lemma 1.16, p. 14

import Definitions.Def_mm_basic

namespace MarkovMixing

/-- **Lemma 1.16** (LPW): a function harmonic at every state of an irreducible
chain is constant. -/
theorem harmonic_eq_const {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (h : V → ℝ) (hh : Harmonic P h) (x y : V) :
    h x = h y := by
  sorry

end MarkovMixing
