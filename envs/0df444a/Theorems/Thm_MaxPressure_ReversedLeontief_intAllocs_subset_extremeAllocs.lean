-- Prove2me | Theorems.Thm_MaxPressure_ReversedLeontief_intAllocs_subset_extremeAllocs
-- name    : MaxPressure.ReversedLeontief.intAllocs_subset_extremeAllocs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:06:49.934826+00:00
-- url     : https://prove2.me/theorems/4032fcac-31ac-4be5-90b9-ba307d6535a9
-- title:
--   Proof of Lemma 1, p. 215 — every feasible integer allocation is extreme, $\mathcal N\subseteq\mathcal E$
-- statement:
--   In a stochastic processing network satisfying the standing assumptions of §2, every feasible integer allocation is an extreme allocation:
--   $$\mathcal N\subseteq\mathcal E.$$
--   Here $\mathcal N$ is the set of allocations $a\in\mathbb Z^J_+$ satisfying (1) and (2), and $\mathcal E$ the set of extreme points of the allocation set $\mathcal A$.
--
--   This is one inclusion of Lemma 1; §7 (p. 206) records it for every network ("each allocation in $\mathcal N$ is an extreme one").
--
--   **Formalization Note.** The reversed Leontief hypothesis is not assumed: the inclusion holds for every network satisfying the standing assumptions, as §7 states.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 215, Appendix B, proof of Lemma 1, last sentence; p. 206, §7

import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network

namespace MaxPressure.ReversedLeontief

/-- §7, p. 206, and proof of Lemma 1, p. 215: every feasible integer allocation is extreme,
`𝒩 ⊆ ℰ`. (The page states it for every network in §7; reversed Leontief is not needed.) -/
theorem intAllocs_subset_extremeAllocs {I J K : ℕ} (N : Network I J K) (hN : N.Standing) :
    intAllocs N ⊆ extremeAllocs N := by sorry

end MaxPressure.ReversedLeontief
