-- Prove2me | Theorems.Thm_MarkovMixing_cftp_coalescence
-- name    : MarkovMixing.cftp_coalescence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:45:34.945115+00:00
-- url     : https://prove2.me/theorems/be6aa043-c2cb-4d90-8f19-bdd5ce49b512
-- title:
--   Coalescence is almost sure
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$, and let $\nu$ be a **random mapping representation** of $P$: a probability distribution on update functions $f:V\to V$ with $\nu\{f:f(x)=y\}=P(x,y)$ for all $x,y$. **Coupling from the past** composes i.i.d. maps drawn from $\nu$ at times $-1,-2,\dots$ forward to time zero, $F^0_{-t}=f_{-1}\circ\cdots\circ f_{-t}$, and the composition has **coalesced** when it is a constant map — all starting states have been funneled to one common value.
--
--   The theorem (§22.3 of Levin–Peres–Wilmer) asserts: if *some* finite block of updates collapses the state space with positive probability — there is a $t_0$ and a tuple of maps $(g_1,\dots,g_{t_0})$, each of positive $\nu$-probability, whose composition is constant — then coalescence is almost sure:
--   $$\mathbb P\bigl\{F^0_{-t}\ \text{not yet constant}\bigr\}\;\longrightarrow\;0\qquad(t\to\infty).$$
--
--   The proof is a geometric-trials argument: the past divides into disjoint blocks of length $t_0$, each an independent chance of at least $p=\prod_i\nu(g_i)>0$ to collapse everything, and one collapsed block anywhere inside the composition makes the whole composition constant. This is the standing hypothesis of the correctness theorem — and the reason CFTP terminates in practice: for an irreducible aperiodic chain a collapsing block always exists, so the algorithm halts with probability one.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 22.3, pp. 291-292

import Definitions.Def_mm_cftp
import Mathlib.Analysis.SpecificLimits.Basic

namespace MarkovMixing

/-- **§22.3** (LPW): if some finite composition of update maps collapses the
state space with positive probability, then coalescence is almost sure: the
probability that CFTP has not coalesced by time `t` tends to `0`. -/
theorem cftp_coalescence {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (ν : (V → V) → ℝ) (hν : IsRandomMapRep P ν)
    (hpos : ∃ (t : ℕ) (F : Fin t → (V → V)),
      0 < ∏ i, ν (F i) ∧ ∀ x y : V, cftpCompose F x = cftpCompose F y) :
    Filter.Tendsto (fun t => cftpNotCoalescedProb ν t)
      Filter.atTop (nhds 0) := by
  sorry

end MarkovMixing
