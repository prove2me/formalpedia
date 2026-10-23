-- Prove2me | Theorems.Thm_LearnAugFL_CMP_lemma_27
-- name    : LearnAugFL.CMP.lemma_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:45.051547+00:00
-- url     : https://prove2.me/theorems/3985c284-bc61-4337-8ae3-1e822c6c3826
-- title:
--   Lemma 27, p. 23 — moving a point towards the optimum without changing CMP's output strictly worsens a ratio above 1
-- statement:
--   Throughout, $\mathbb R^2$ carries the Euclidean distance $d$; $P=(p_1,\dots,p_n)$ is a profile of $n\ge 1$ preferred locations; $c\in[0,1)$ is a confidence parameter with $cn$ an integer; $C^u(f,P)=\frac1n\sum_{i=1}^n d(f,p_i)$ is the utilitarian social cost; $o(P)$ is an optimal (cost-minimizing) location; and $f(P,\hat o,c)$ is the location chosen by the Coordinatewise Median with Predictions (CMP): each coordinate is the lower median of the $n+cn$ values formed by the agents' coordinates and $cn$ copies of the prediction's coordinate. The ratio is $r(P,\hat o,c)=C^u(f(P,\hat o,c),P)/C^u(o(P),P)$.
--
--   Fix $c\in[0,1)$, a prediction $\hat o$, a profile $P$ with optimal location $o$, an agent $i$ with $p_i\neq o$, and $p'_i=p_i+s(o-p_i)$ with $s\in(0,1]$ (a point of the segment $(p_i,o]$). If CMP's output does not change, $f(P,\hat o,c)=f((P_{-i},p'_i),\hat o,c)$, and $r(P,\hat o,c)>1$, then
--   $$r\big((P_{-i},p'_i),\hat o,c\big)>r(P,\hat o,c),$$
--   where both ratios are measured against $o$ (which remains optimal for the new profile by Lemma 26).
--
--   The lemma drives every "move a point towards the optimum" step of the worst-case reduction.
--
--   **Formalization Note** The optimal location $o(P)$ is taken as any $o$ with `IsOpt P o` (a minimizer of $C^u(\cdot,P)$; it is unique unless the points are collinear). The confidence enters through `Admissible c n k`: $n\ge1$ and $k=cn$ copies of the prediction. Ratios are real quotients `ratio P ô o k`; on every family used here the optimal cost is positive (if all points sat at $o(P)$, CMP would return $o(P)$ because $cn<n$), so no ratio is a junk $0/0$. The hypothesis $p_i\ne o$ makes the segment $(p_i,o]$ nonempty, as the page presupposes.
-- source:
--   Agrawal, Balkanski, Gkatzelis, Ou & Tan, Learning-Augmented Mechanism Design: Leveraging Predictions for Facility Location, arXiv:2204.01120v1, Lemma 27, p. 23

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

namespace LearnAugFL.CMP

theorem lemma_27 (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {n k : ℕ} (hnk : Admissible c n k)
    (P : Fin n → Pt) (ô o : Pt) (hP : IsOpt P o) (i : Fin n) (hi : P i ≠ o)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hf : cmp P ô k = cmp (Function.update P i (P i + s • (o - P i))) ô k)
    (hr : 1 < ratio P ô o k) :
    ratio P ô o k < ratio (Function.update P i (P i + s • (o - P i))) ô o k := by sorry
end LearnAugFL.CMP
