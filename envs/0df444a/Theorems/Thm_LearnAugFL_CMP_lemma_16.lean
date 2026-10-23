-- Prove2me | Theorems.Thm_LearnAugFL_CMP_lemma_16
-- name    : LearnAugFL.CMP.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:44.629618+00:00
-- url     : https://prove2.me/theorems/c1c2a423-8841-47ca-bf56-5d914e6527a2
-- title:
--   Lemma 16, p. 20 — too many points on the negative half-axis: there is a strictly worse instance
-- statement:
--   Throughout, $\mathbb R^2$ carries the Euclidean distance $d$; $P=(p_1,\dots,p_n)$ is a profile of $n\ge 1$ preferred locations; $c\in[0,1)$ is a confidence parameter with $cn$ an integer; $C^u(f,P)=\frac1n\sum_{i=1}^n d(f,p_i)$ is the utilitarian social cost; $o(P)$ is an optimal (cost-minimizing) location; and $f(P,\hat o,c)$ is the location chosen by the Coordinatewise Median with Predictions (CMP): each coordinate is the lower median of the $n+cn$ values formed by the agents' coordinates and $cn$ copies of the prediction's coordinate. The ratio is $r(P,\hat o,c)=C^u(f(P,\hat o,c),P)/C^u(o(P),P)$.
--
--   Let $c\in[0,1)$, let $P$ be a profile with optimal location $o=(x_o,y_o)$, $y_o\ge x_o>0$, whose points all lie on $A_x\cup A_y\cup\{o\}$. Suppose
--   $$\big|\{i:p_i\in A^<_{-x}\}\big|\ \ge\ \big|\{i:p_i\in A^>_{+x}\cup\{o\}\}\big|\quad\text{or}\quad\big|\{i:p_i\in A^<_{-y}\}\big|\ \ge\ \big|\{i:p_i\in A^>_{+y}\cup\{o\}\}\big|.$$
--   Then:
--
--   1. (consistency) if $f(P,o,c)=(0,0)$, there is an instance $Q$ with optimal location $o_Q$ and $r(Q,o_Q,c)>r(P,o,c)$;
--   2. (robustness) if $f(P,(0,0),c)=(0,0)$, there is an instance $Q$ with optimal location $o_Q$ and $r(Q,(0,0),c)>r(P,(0,0),c)$.
--
--   The lemma yields the counting properties 4(b)–(c) of the CA family.
--
--   **Formalization Note** The optimal location $o(P)$ is taken as any $o$ with `IsOpt P o` (a minimizer of $C^u(\cdot,P)$; it is unique unless the points are collinear). The confidence enters through `Admissible c n k`: $n\ge1$ and $k=cn$ copies of the prediction. Ratios are real quotients `ratio P ô o k`; on every family used here the optimal cost is positive (if all points sat at $o(P)$, CMP would return $o(P)$ because $cn<n$), so no ratio is a junk $0/0$. Points are counted with multiplicity (one per agent).
-- source:
--   Agrawal, Balkanski, Gkatzelis, Ou & Tan, Learning-Augmented Mechanism Design: Leveraging Predictions for Facility Location, arXiv:2204.01120v1, Lemma 16, p. 20 (proof pp. 24–25)

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

namespace LearnAugFL.CMP

theorem lemma_16 (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {n k : ℕ} (hnk : Admissible c n k)
    (P : Fin n → Pt) (o : Pt) (hP : IsOpt P o) (ho0 : 0 < o 0) (ho01 : o 0 ≤ o 1)
    (haxes : ∀ i, onX (P i) ∨ onY (P i) ∨ P i = o)
    (hcount : count P (fun p => posX' p ∨ p = o) ≤ count P negX' ∨
      count P (fun p => posY' p ∨ p = o) ≤ count P negY') :
    (cmp P o k = 0 → ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt),
        Admissible c m k' ∧ IsOpt Q oQ ∧ ratio P o o k < ratio Q oQ oQ k') ∧
    (cmp P 0 k = 0 → ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt),
        Admissible c m k' ∧ IsOpt Q oQ ∧ ratio P 0 o k < ratio Q 0 oQ k') := by sorry
end LearnAugFL.CMP
