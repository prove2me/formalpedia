-- Prove2me | Theorems.Thm_LearnAugFL_CMP_lemma_18
-- name    : LearnAugFL.CMP.lemma_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:55.801984+00:00
-- url     : https://prove2.me/theorems/2c8c9db0-8d67-44b9-876d-23e6f9b661a2
-- title:
--   Lemma 18, pp. 20–21 — from an OA instance to a COA instance without improving the ratio
-- statement:
--   Throughout, $\mathbb R^2$ carries the Euclidean distance $d$; $P=(p_1,\dots,p_n)$ is a profile of $n\ge 1$ preferred locations; $c\in[0,1)$ is a confidence parameter with $cn$ an integer; $C^u(f,P)=\frac1n\sum_{i=1}^n d(f,p_i)$ is the utilitarian social cost; $o(P)$ is an optimal (cost-minimizing) location; and $f(P,\hat o,c)$ is the location chosen by the Coordinatewise Median with Predictions (CMP): each coordinate is the lower median of the $n+cn$ values formed by the agents' coordinates and $cn$ copies of the prediction's coordinate. The ratio is $r(P,\hat o,c)=C^u(f(P,\hat o,c),P)/C^u(o(P),P)$.
--
--   Fix $c\in[0,1)$.
--
--   1. (consistency) For every $P\in\mathcal P^C_{oa}(c)$ with optimal location $o$ there is an instance $Q$ with optimal location $o_Q$ such that either $r(Q,o_Q,c)>r(P,o,c)$, or $Q\in\mathcal P^C_{coa}(c)$ (so $o_Q=(0,1)$) and $r(Q,o_Q,c)\ge r(P,o,c)$.
--   2. (robustness) For every $P\in\mathcal P^R_{oa}(c)$ with optimal location $o$ there is $Q$ with optimal location $o_Q$ such that either $r(Q,(0,0),c)>r(P,(0,0),c)$, or $Q\in\mathcal P^R_{coa}(c)$ and $r(Q,(0,0),c)\ge r(P,(0,0),c)$.
--
--   Together with Lemmas 24–25 this moves the worst case into the COA family.
--
--   **Formalization Note** The optimal location $o(P)$ is taken as any $o$ with `IsOpt P o` (a minimizer of $C^u(\cdot,P)$; it is unique unless the points are collinear). The confidence enters through `Admissible c n k`: $n\ge1$ and $k=cn$ copies of the prediction. Ratios are real quotients `ratio P ô o k`; on every family used here the optimal cost is positive (if all points sat at $o(P)$, CMP would return $o(P)$ because $cn<n$), so no ratio is a junk $0/0$. The page's robustness clause contains the typo "r(P, (0, 0, c)", read as $r(P,(0,0),c)$.
-- source:
--   Agrawal, Balkanski, Gkatzelis, Ou & Tan, Learning-Augmented Mechanism Design: Leveraging Predictions for Facility Location, arXiv:2204.01120v1, Lemma 18, pp. 20–21

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

namespace LearnAugFL.CMP

theorem lemma_18 (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∀ (n k : ℕ) (P : Fin n → Pt) (o : Pt), OA_C c n k P o →
      ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), Admissible c m k' ∧ IsOpt Q oQ ∧
        (ratio P o o k < ratio Q oQ oQ k' ∨
          (COA_C c m k' Q ∧ oQ = !₂[0, 1] ∧ ratio P o o k ≤ ratio Q oQ oQ k'))) ∧
    (∀ (n k : ℕ) (P : Fin n → Pt) (o : Pt), OA_R c n k P o →
      ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), Admissible c m k' ∧ IsOpt Q oQ ∧
        (ratio P 0 o k < ratio Q 0 oQ k' ∨
          (COA_R c m k' Q ∧ oQ = !₂[0, 1] ∧ ratio P 0 o k ≤ ratio Q 0 oQ k'))) := by sorry
end LearnAugFL.CMP
