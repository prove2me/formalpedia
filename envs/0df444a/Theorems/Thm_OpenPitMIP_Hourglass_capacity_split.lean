-- Prove2me | Theorems.Thm_OpenPitMIP_Hourglass_capacity_split
-- name    : OpenPitMIP.Hourglass.capacity_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:56:39.085457+00:00
-- url     : https://prove2.me/theorems/2210dc60-a4b4-494f-b5eb-926f30bbac5c
-- title:
--   Proof of Theorem 8, p. 1435 — predecessors S, the blocks of c̄ and b(R) share the capacity U_s^d of destination d
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions. Fix a destination $d$, a cluster $\bar c$, a set $S\subseteq b(cl(\bar c)\setminus\{\bar c\})$ of blocks of strict predecessors of $\bar c$, and let $R=rcl(\bar c)\setminus\{\bar c\}$. If $y\ge 0$ satisfies the destination capacity rows (9), $\sum_{b}q_b y_{b,d,s}\le U^d_s$, then for every period $s$
--   $$\sum_{b\in S}q_b\,y_{b,d,s}+\sum_{b\in\bar c}q_b\,y_{b,d,s}+\sum_{b\in b(R)}q_b\,y_{b,d,s}\le U^d_s .$$
--
--   This is the capacity inequality from which the proof of Theorem 8 starts, before summing over $s=t_1,\dots,t$.
--
--   **Formalization Note** The page writes "$\forall s\le t$"; the inequality holds for every period $s$ and is stated so. Only nonnegativity of $y$ and the rows (9) are assumed about $y$.
-- source:
--   Oper. Res. 68(5), proof of Theorem 8, p. 1435

import Mathlib
import Definitions.Def_OpenPitMIP_Hourglass_Setting

namespace OpenPitMIP.Hourglass

/-- Proof of Theorem 8, p. 1435: for a cluster `c̄`, a set `S` of blocks of strict predecessors of
`c̄` and `R = rcl(c̄) \ {c̄}`, every nonnegative `y` satisfying the destination capacity rows (9)
satisfies, for every period `s`,
`∑_{b∈S} q_b y_{b,d,s} + ∑_{b∈c̄} q_b y_{b,d,s} + ∑_{b∈b(R)} q_b y_{b,d,s} ≤ U_s^d`. -/
theorem capacity_split {B D C : Type} [Fintype B] [Fintype D] [Fintype C]
    [DecidableEq B] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (d : D) (cbar : C) (S : Finset B)
    (hS : S ⊆ I.blocksOf (I.cl cbar \ {cbar}))
    (y : B → D → Fin T → ℝ) (hy0 : ∀ b d t, 0 ≤ y b d t) (hcap : I.DestCap y) :
    ∀ s : Fin T,
      ∑ b ∈ S, I.q b * y b d s + ∑ b ∈ I.blocksOf {cbar}, I.q b * y b d s
        + ∑ b ∈ I.blocksOf (I.rcl cbar \ {cbar}), I.q b * y b d s ≤ I.Ud d s := by sorry

end OpenPitMIP.Hourglass
