-- Prove2me | Theorems.Thm_MarkovMixing_monotone_cftp_coalescence
-- name    : MarkovMixing.monotone_cftp_coalescence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:45:47.683093+00:00
-- url     : https://prove2.me/theorems/48652085-c8eb-4e6f-987e-c42ca744170f
-- title:
--   Monotone CFTP: two trajectories certify coalescence
-- statement:
--   Let $V$ be a finite state space carrying a partial order with a smallest element $\hat 0$ and a largest element $\hat 1$, and let $g_1,\dots,g_t:V\to V$ be **monotone** maps: $u\le v$ implies $g_i(u)\le g_i(v)$. Write $\Phi=g_1\circ g_2\circ\cdots\circ g_t$ for their composition (as in coupling from the past, where the $g_i$ are the update maps drawn at times $-1,\dots,-t$ and the deepest map applies first).
--
--   The theorem (§22.2 of Levin–Peres–Wilmer, the principle behind **monotone CFTP**) asserts: if the composition merely identifies the two extremes,
--   $$\Phi(\hat 0)=\Phi(\hat 1),$$
--   then $\Phi$ is constant on all of $V$: $\Phi(x)=\Phi(y)$ for every pair of states.
--
--   A composition of monotone maps is monotone, so $\Phi(\hat 0)\le\Phi(x)\le\Phi(\hat 1)$ for every $x$; when the two ends meet, everything between is squeezed to the same value. This is what makes CFTP practical on exponentially large ordered state spaces: instead of tracking all $|V|$ trajectories, the algorithm runs just two — from the top state and the bottom state — and their meeting certifies global coalescence. For the Ising model of Mission IX, whose heat-bath updates are monotone for the coordinatewise spin order, this reduces $2^n$ trajectories to $2$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 22.2, pp. 288-290

import Definitions.Def_mm_cftp
import Mathlib.Order.Bounds.Basic

namespace MarkovMixing

/-- **§22.2, monotone CFTP** (LPW): if the state space carries a partial
order with a top and a bottom state and every update map is monotone, then
the composition collapses the whole space as soon as it identifies the top
and bottom states — the upper and lower trajectories of the monotone CFTP
algorithm sandwich all others. -/
theorem monotone_cftp_coalescence {V : Type*} [Fintype V] [DecidableEq V]
    [PartialOrder V] [OrderBot V] [OrderTop V]
    {t : ℕ} (F : Fin t → (V → V)) (hmono : ∀ i, Monotone (F i))
    (hmeet : cftpCompose F ⊥ = cftpCompose F ⊤) :
    ∀ x y : V, cftpCompose F x = cftpCompose F y := by
  sorry

end MarkovMixing
