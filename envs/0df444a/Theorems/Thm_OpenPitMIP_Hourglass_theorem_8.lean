-- Prove2me | Theorems.Thm_OpenPitMIP_Hourglass_theorem_8
-- name    : OpenPitMIP.Hourglass.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:44.850727+00:00
-- url     : https://prove2.me/theorems/4da5a3e0-cdbd-409f-b403-8369f251c96f
-- title:
--   Theorem 8, p. 1435 — the hourglass cut (37) is valid for the PCPSP-C under full and partial integrality
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions (clusters partition the blocks, $\prec$ is a strict partial order on clusters, $r>0$, $q\ge 0$). Let $d$ be a destination, $1\le t_1\le t\le T$, $\bar c\in\mathcal C$, and let $S\subseteq b(cl(\bar c)\setminus\{\bar c\})$ be a set of blocks of strict predecessors of $\bar c$ such that
--   $$q(S)\ge\sum_{s=t_1}^{t}U^d_s .$$
--   Let $R=rcl(\bar c)\setminus\{\bar c\}$. Then the inequality
--   $$\Bigl(q(S\cup\{\bar c\})-\sum_{s=t_1}^{t}U^d_s\Bigr)w_{\bar c,t}+\sum_{b\in b(R)}q_b\sum_{s=t_1}^{t}y_{b,d,s}\le\sum_{b\in S\cup\{\bar c\}}q_b\Bigl(w_{c(b),t}-\sum_{s=t_1}^{t}y_{b,d,s}\Bigr)\tag{37}$$
--   is valid for the PCPSP-C: it holds at every feasible solution $(x,y)$ of the PCPSP-F and of the PCPSP-P whose destination capacity rows (9) hold, with $w_{c,t}=\sum_{t'=1}^{t}x_{c,t'}$. Here $S\cup\{\bar c\}$ is the set of blocks of $S$ together with the blocks of $\bar c$, and $q(\cdot)$ of a block set is the sum of its weights.
--
--   The hourglass cuts couple the predecessors and successors of a cluster through a destination's capacity; they are not valid for the LP relaxation and are used to strengthen it.
--
--   **Formalization Note** "Valid for PCPSP-C" is read as valid under both integrality conditions (10) and (11). The capacity rows (9) are assumed explicitly, which is the page's assumption that they are among the rows $Gy\le g$. The destination $d$, left unbound on the page, is a fixed arbitrary destination. Periods are `Fin T`, so index $t$ is period $t+1$ and $t_1\le t$ is $1\le t_1\le t\le T$.
-- source:
--   Oper. Res. 68(5), Theorem 8 and (37), §5.2.3, p. 1435

import Mathlib
import Definitions.Def_OpenPitMIP_Hourglass_Setting

namespace OpenPitMIP.Hourglass

/-- Theorem 8 (hourglass cuts), p. 1435. Let `1 ≤ t₁ ≤ t ≤ T`, `d` a destination, `c̄` a cluster
and `S ⊆ b(cl(c̄) \ {c̄})` a set of blocks with `q(S) ≥ ∑_{s=t₁}^{t} U_s^d`; let `R = rcl(c̄) \ {c̄}`.
Then inequality (37),
`(q(S ∪ {c̄}) − ∑_{s=t₁}^{t} U_s^d) w_{c̄,t} + ∑_{b∈b(R)} q_b ∑_{s=t₁}^{t} y_{b,d,s}
  ≤ ∑_{b∈S∪{c̄}} q_b (w_{c(b),t} − ∑_{s=t₁}^{t} y_{b,d,s})`,
is valid for PCPSP-C: it holds at every feasible point of the PCPSP-F and of the PCPSP-P whose
destination capacity rows (9) hold. `S ∪ {c̄}` is the block set `S ∪ b({c̄})`. -/
theorem theorem_8 {B D C : Type} [Fintype B] [Fintype D] [Fintype C]
    [DecidableEq B] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (d : D) (t₁ t : Fin T) (ht : t₁ ≤ t)
    (cbar : C) (S : Finset B) (hS : S ⊆ I.blocksOf (I.cl cbar \ {cbar}))
    (hqS : I.Ucum d t₁ t ≤ I.qBlocks S) :
    ∀ (κ : Integrality) (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
      I.Feasible κ x y → I.DestCap y →
        (I.qBlocks (S ∪ I.blocksOf {cbar}) - I.Ucum d t₁ t) * PCPSPC.cum x cbar t
          + ∑ b ∈ I.blocksOf (I.rcl cbar \ {cbar}), I.q b * PCPSPC.ySum y b d t₁ t
        ≤ ∑ b ∈ S ∪ I.blocksOf {cbar},
            I.q b * (PCPSPC.cum x (I.clu b) t - PCPSPC.ySum y b d t₁ t) := by sorry

end OpenPitMIP.Hourglass
