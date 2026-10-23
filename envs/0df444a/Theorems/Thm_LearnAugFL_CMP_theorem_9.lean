-- Prove2me | Theorems.Thm_LearnAugFL_CMP_theorem_9
-- name    : LearnAugFL.CMP.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:49.191028+00:00
-- url     : https://prove2.me/theorems/96c29a42-b86c-4ef8-941c-858b5bb6c5e9
-- title:
--   Theorem 9, p. 14 — CMP with confidence c ∈ [0,1) is √(2c²+2)/(1+c)-consistent and √(2c²+2)/(1−c)-robust for the utilitarian cost
-- statement:
--   Throughout, $\mathbb R^2$ carries the Euclidean distance $d$; $P=(p_1,\dots,p_n)$ is a profile of $n\ge 1$ preferred locations; $c\in[0,1)$ is a confidence parameter with $cn$ an integer; $C^u(f,P)=\frac1n\sum_{i=1}^n d(f,p_i)$ is the utilitarian social cost; $o(P)$ is an optimal (cost-minimizing) location; and $f(P,\hat o,c)$ is the location chosen by the Coordinatewise Median with Predictions (CMP): each coordinate is the lower median of the $n+cn$ values formed by the agents' coordinates and $cn$ copies of the prediction's coordinate. The ratio is $r(P,\hat o,c)=C^u(f(P,\hat o,c),P)/C^u(o(P),P)$.
--
--   Let $c\in[0,1)$, let $n\ge1$ with $cn$ an integer, and let $P=(p_1,\dots,p_n)$ be any profile of points in $\mathbb R^2$.
--
--   1. **Consistency.** For every optimal location $o$ of $P$, when the prediction is correct ($\hat o=o$),
--   $$C^u\big(f(P,o,c),P\big)\ \le\ \frac{\sqrt{2c^2+2}}{1+c}\,C^u(o,P).$$
--   2. **Robustness.** For every prediction $\hat o\in\mathbb R^2$ and every optimal location $o$ of $P$,
--   $$C^u\big(f(P,\hat o,c),P\big)\ \le\ \frac{\sqrt{2c^2+2}}{1-c}\,C^u(o,P).$$
--
--   At $c=0$ CMP is the coordinatewise median and both bounds equal $\sqrt2$; as $c\to1$ consistency approaches $1$ while robustness degrades. Lemma 8 shows both bounds are attained.
--
--   **Formalization Note** The approximation-ratio statements $\max_P C(f(P,o(P)),P)/C(o(P),P)\le\alpha$ are cross-multiplied, which avoids the $0/0$ of a unanimous profile (where both sides are $0$). The maximum over $P$ ranges over all $n\ge1$ with $cn$ an integer (`Admissible c n k`, $k=cn$ copies of the prediction). The optimal location is any minimizer `IsOpt P o` of $C^u(\cdot,P)$; the consistency clause holds for each of them. CMP uses the lower median of the $n+cn$ values, as in the paper.
-- source:
--   Agrawal, Balkanski, Gkatzelis, Ou & Tan, Learning-Augmented Mechanism Design: Leveraging Predictions for Facility Location, arXiv:2204.01120v1, Theorem 9, p. 14 (proof pp. 14–15)

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

namespace LearnAugFL.CMP

theorem theorem_9 (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (n k : ℕ) (hnk : Admissible c n k)
    (P : Fin n → Pt) :
    (∀ o : Pt, IsOpt P o →
        ucost P (cmp P o k) ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 + c) * ucost P o) ∧
    (∀ ô o : Pt, IsOpt P o →
        ucost P (cmp P ô k) ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 - c) * ucost P o) := by sorry
end LearnAugFL.CMP
