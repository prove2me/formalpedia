-- Prove2me | Theorems.Thm_OpenPitMIP_Hourglass_most_violated_set
-- name    : OpenPitMIP.Hourglass.most_violated_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:30.032641+00:00
-- url     : https://prove2.me/theorems/9adeab90-4682-4faa-90fe-1975ed78e3e7
-- title:
--   (38), p. 1436 — the block set S* = {b : c(b) ≺ c̄, w*_{c̄,t} > w*_{c(b),t} − ∑ y*_{b,d,s}} maximizes the violation of (37)
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions, arbitrary values $w^*_{c,t}$ and $y^*_{b,d,t}$ (for instance a solution of the LP relaxation), a cluster $\bar c$, a destination $d$ and periods $1\le t_1\le t\le T$. For a set $S$ of blocks let
--   $$\mathrm{viol}(S)=\Bigl(q(S\cup\{\bar c\})-\sum_{s=t_1}^{t}U^d_s\Bigr)w^*_{\bar c,t}+\sum_{b\in b(R)}q_b\sum_{s=t_1}^{t}y^*_{b,d,s}-\sum_{b\in S\cup\{\bar c\}}q_b\Bigl(w^*_{c(b),t}-\sum_{s=t_1}^{t}y^*_{b,d,s}\Bigr)$$
--   be the violation of the hourglass inequality (37), with $R=rcl(\bar c)\setminus\{\bar c\}$ and $S\cup\{\bar c\}$ the blocks of $S$ together with those of $\bar c$. Then the set
--   $$S^*=\Bigl\{b\in\mathcal B:\ c(b)\prec\bar c,\ w^*_{\bar c,t}>w^*_{c(b),t}-\sum_{s=t_1}^{t}y^*_{b,d,s}\Bigr\}\tag{38}$$
--   satisfies $S^*\subseteq b(cl(\bar c)\setminus\{\bar c\})$, and $\mathrm{viol}(S)\le\mathrm{viol}(S^*)$ for every $S\subseteq b(cl(\bar c)\setminus\{\bar c\})$.
--
--   This makes the separation of the most violated hourglass cut, for fixed $\bar c,d,t_1,t$, a simple pass over the blocks.
--
--   **Formalization Note** The page says $S^*$ "maximizes the violation"; with ties the maximizer is not unique, so the statement is that $S^*$ attains the maximum. The maximum is over all $S\subseteq b(cl(\bar c)\setminus\{\bar c\})$, as on the page; the side condition $q(S)\ge\sum_{s=t_1}^{t}U^d_s$ of Theorem 8 is not imposed, and $S^*$ need not satisfy it. No feasibility is assumed of $(w^*,y^*)$.
-- source:
--   Oper. Res. 68(5), display (38), §5.2.3, p. 1436

import Mathlib
import Definitions.Def_OpenPitMIP_Hourglass_Setting

namespace OpenPitMIP.Hourglass

open Classical in
/-- Display (38), p. 1436: the most violated hourglass cut. For arbitrary values `w*` and `y*`
(for instance a solution of the LP relaxation), a cluster `c̄`, a destination `d` and periods
`t₁ ≤ t`, let `viol S` be the left-hand side minus the right-hand side of (37) at `(w*, y*)`.
The block set `S* = {b : c(b) ≺ c̄, w*_{c̄,t} > w*_{c(b),t} − ∑_{s=t₁}^{t} y*_{b,d,s}}` is admissible,
`S* ⊆ b(cl(c̄) \ {c̄})`, and attains the maximum of `viol` over all `S ⊆ b(cl(c̄) \ {c̄})`. -/
theorem most_violated_set {B D C : Type} [Fintype B] [Fintype D] [Fintype C]
    [DecidableEq B] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing)
    (w : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (cbar : C) (d : D)
    (t₁ t : Fin T) (ht : t₁ ≤ t) :
    let viol : Finset B → ℝ := fun S =>
      (I.qBlocks (S ∪ I.blocksOf {cbar}) - I.Ucum d t₁ t) * w cbar t
        + ∑ b ∈ I.blocksOf (I.rcl cbar \ {cbar}), I.q b * PCPSPC.ySum y b d t₁ t
        - ∑ b ∈ S ∪ I.blocksOf {cbar}, I.q b * (w (I.clu b) t - PCPSPC.ySum y b d t₁ t)
    let Sstar : Finset B := Finset.univ.filter
      (fun b => I.cprec (I.clu b) cbar ∧ w (I.clu b) t - PCPSPC.ySum y b d t₁ t < w cbar t)
    Sstar ⊆ I.blocksOf (I.cl cbar \ {cbar}) ∧
      ∀ S ⊆ I.blocksOf (I.cl cbar \ {cbar}), viol S ≤ viol Sstar := by sorry

end OpenPitMIP.Hourglass
