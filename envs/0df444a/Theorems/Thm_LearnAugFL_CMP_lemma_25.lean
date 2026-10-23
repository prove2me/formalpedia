-- Prove2me | Theorems.Thm_LearnAugFL_CMP_lemma_25
-- name    : LearnAugFL.CMP.lemma_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:49.657872+00:00
-- url     : https://prove2.me/theorems/5deacb3d-ba33-4ca7-9196-df00a8616fee
-- title:
--   Lemma 25, p. 22 — from a CA instance to a COA instance without improving robustness
-- statement:
--   Throughout, $\mathbb R^2$ carries the Euclidean distance $d$; $P=(p_1,\dots,p_n)$ is a profile of $n\ge 1$ preferred locations; $c\in[0,1)$ is a confidence parameter with $cn$ an integer; $C^u(f,P)=\frac1n\sum_{i=1}^n d(f,p_i)$ is the utilitarian social cost; $o(P)$ is an optimal (cost-minimizing) location; and $f(P,\hat o,c)$ is the location chosen by the Coordinatewise Median with Predictions (CMP): each coordinate is the lower median of the $n+cn$ values formed by the agents' coordinates and $cn$ copies of the prediction's coordinate. The ratio is $r(P,\hat o,c)=C^u(f(P,\hat o,c),P)/C^u(o(P),P)$.
--
--   Fix $c\in[0,1)$. For every $P\in\mathcal P^R_{ca}(c)$ with optimal location $o$ there are an instance $Q$ with optimal location $o_Q$ and a prediction $\hat o$ such that either
--   $$r(Q,\hat o,c)>r(P,(0,0),c)\qquad\text{or}\qquad Q\in\mathcal P^R_{coa}(c)\ \text{and}\ r(Q,(0,0),c)\ge r(P,(0,0),c).$$
--
--   This is the robustness half of the CA-to-COA step; in the strict branch the prediction is arbitrary, as printed.
--
--   **Formalization Note** The optimal location $o(P)$ is taken as any $o$ with `IsOpt P o` (a minimizer of $C^u(\cdot,P)$; it is unique unless the points are collinear). The confidence enters through `Admissible c n k`: $n\ge1$ and $k=cn$ copies of the prediction. Ratios are real quotients `ratio P ô o k`; on every family used here the optimal cost is positive (if all points sat at $o(P)$, CMP would return $o(P)$ because $cn<n$), so no ratio is a junk $0/0$.
-- source:
--   Agrawal, Balkanski, Gkatzelis, Ou & Tan, Learning-Augmented Mechanism Design: Leveraging Predictions for Facility Location, arXiv:2204.01120v1, Lemma 25, p. 22 (proof pp. 31–32)

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

namespace LearnAugFL.CMP

theorem lemma_25 (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {n k : ℕ} (P : Fin n → Pt) (o : Pt)
    (hP : CA_R c n k P o) :
    ∃ (m k' : ℕ) (Q : Fin m → Pt) (ô oQ : Pt), Admissible c m k' ∧ IsOpt Q oQ ∧
      (ratio P 0 o k < ratio Q ô oQ k' ∨
        (COA_R c m k' Q ∧ oQ = !₂[0, 1] ∧ ratio P 0 o k ≤ ratio Q 0 oQ k')) := by sorry
end LearnAugFL.CMP
