-- Prove2me | Theorems.Thm_MarkovMixing_cftp_correct
-- name    : MarkovMixing.cftp_correct
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:46:00.082189+00:00
-- url     : https://prove2.me/theorems/1a70190d-4afd-4a31-87d2-29b0d6a8e695
-- title:
--   Correctness of coupling from the past (Propp--Wilson)
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$ with stationary distribution $\pi$, and let $\nu$ be a **random mapping representation** of $P$: a probability distribution on update functions $f:V\to V$ with $\nu\{f:f(x)=y\}=P(x,y)$ for all $x,y$. **Coupling from the past** draws i.i.d. maps $f_{-1},f_{-2},\dots\sim\nu$ at past times and composes them forward up to time zero,
--   $$F^0_{-t}=f_{-1}\circ f_{-2}\circ\cdots\circ f_{-t}$$
--   (deepening the horizon prepends randomness inside the composition; the maps near time $0$ stay fixed). The composition has **coalesced** when it is a constant map, and the algorithm outputs the common value. Assume coalescence is almost sure: $\mathbb P\{F^0_{-t}\text{ not constant}\}\to0$.
--
--   The theorem (**correctness of coupling from the past**, Propp–Wilson; §22.2–22.3 of Levin–Peres–Wilmer — the capstone of Chapter 22 and of this series) asserts: for every state $y$,
--   $$\mathbb P\bigl\{F^0_{-t}\ \text{coalesced with common value}\ y\bigr\}\;\longrightarrow\;\pi(y)\qquad(t\to\infty).$$
--
--   The output of CFTP is an **exact** sample from the stationary distribution — no mixing-time error, no knowledge of $t_{\mathrm{mix}}$ required. The point is the direction of composition: for fixed $t$ the law of $F^0_{-t}(x)$ is that of $t$ forward steps from $x$, but the coalesced value is *shared* by all $x$, so on the coalescence event the output agrees with a chain started from $\pi$ itself — and the discrepancy is bounded by the vanishing non-coalescence probability. Running the same maps *into the future* instead produces a biased sample; the from-the-past order is what the proof, and the formalization, pin down.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Sections 22.2-22.3, pp. 288-292

import Definitions.Def_mm_cftp
import Mathlib.Analysis.SpecificLimits.Basic

namespace MarkovMixing

/-- **§22.2–22.3, correctness of coupling from the past** (Propp–Wilson;
LPW), the capstone of Chapter 22: if the update maps represent `P`, `π` is
stationary for `P`, and coalescence is almost sure, then the CFTP output is
distributed *exactly* according to `π`: the probability of collapsing to `y`
within `t` steps from the past tends to `π(y)`. -/
theorem cftp_correct {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π)
    (ν : (V → V) → ℝ) (hν : IsRandomMapRep P ν)
    (hcoal : Filter.Tendsto (fun t => cftpNotCoalescedProb ν t)
      Filter.atTop (nhds 0)) (y : V) :
    Filter.Tendsto (fun t => cftpOutputProb ν t y)
      Filter.atTop (nhds (π y)) := by
  sorry

end MarkovMixing
