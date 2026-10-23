-- Prove2me | Theorems.Thm_LearnAugFL_CMP_lemma_8
-- name    : LearnAugFL.CMP.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:50.317965+00:00
-- url     : https://prove2.me/theorems/0ba212b7-c9ec-41c8-aea9-867789c9146f
-- title:
--   Lemma 8, p. 13 — COA instances attaining √(2c²+2)/(1+c) for consistency and √(2c²+2)/(1−c) for robustness
-- statement:
--   Throughout, $\mathbb R^2$ carries the Euclidean distance $d$; $P=(p_1,\dots,p_n)$ is a profile of $n\ge 1$ preferred locations; $c\in[0,1)$ is a confidence parameter with $cn$ an integer; $C^u(f,P)=\frac1n\sum_{i=1}^n d(f,p_i)$ is the utilitarian social cost; $o(P)$ is an optimal (cost-minimizing) location; and $f(P,\hat o,c)$ is the location chosen by the Coordinatewise Median with Predictions (CMP): each coordinate is the lower median of the $n+cn$ values formed by the agents' coordinates and $cn$ copies of the prediction's coordinate. The ratio is $r(P,\hat o,c)=C^u(f(P,\hat o,c),P)/C^u(o(P),P)$.
--
--   Let $c\in[0,1)$ be a confidence for which some instance size is admissible ($cn_0\in\mathbb Z$ for some $n_0\ge1$). Then
--
--   1. there is an instance $P\in\mathcal P^C_{coa}(c)$ with $$r(P,\hat o=o(P),c)=\frac{\sqrt{2c^2+2}}{1+c},$$
--   2. and an instance $Q\in\mathcal P^R_{coa}(c)$ with $$r(Q,\hat o=(0,0),c)=\frac{\sqrt{2c^2+2}}{1-c}.$$
--
--   In the paper the instances are: $\frac{1+c}{4}n$ points at each of $(\mp\frac{1+c}{1-c},0)$ and $\frac{1-c}{2}n$ at $(0,1)$; respectively $\frac{1-c}{4}n$ at each of $(\mp\frac{1-c}{1+c},0)$ and $\frac{1+c}{2}n$ at $(0,1)$. They show that the bounds of Theorem 9 are tight.
--
--   **Formalization Note** The optimal location $o(P)$ is taken as any $o$ with `IsOpt P o` (a minimizer of $C^u(\cdot,P)$; it is unique unless the points are collinear). The confidence enters through `Admissible c n k`: $n\ge1$ and $k=cn$ copies of the prediction. Ratios are real quotients `ratio P ô o k`; on every family used here the optimal cost is positive (if all points sat at $o(P)$, CMP would return $o(P)$ because $cn<n$), so no ratio is a junk $0/0$. The page quantifies over all $c\in[0,1)$ but every instance requires $cn\in\mathbb Z$; the hypothesis that some $n_0$ makes $cn_0$ an integer (i.e. $c$ is rational) is that standing assumption made explicit. The instances may have any number of agents.
-- source:
--   Agrawal, Balkanski, Gkatzelis, Ou & Tan, Learning-Augmented Mechanism Design: Leveraging Predictions for Facility Location, arXiv:2204.01120v1, Lemma 8, p. 13 (proof pp. 13–14)

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

namespace LearnAugFL.CMP

theorem lemma_8 (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hc : ∃ n₀ k₀ : ℕ, Admissible c n₀ k₀) :
    (∃ (n k : ℕ) (P : Fin n → Pt), COA_C c n k P ∧
        ratio P !₂[0, 1] !₂[0, 1] k = Real.sqrt (2 * c ^ 2 + 2) / (1 + c)) ∧
    (∃ (n k : ℕ) (Q : Fin n → Pt), COA_R c n k Q ∧
        ratio Q 0 !₂[0, 1] k = Real.sqrt (2 * c ^ 2 + 2) / (1 - c)) := by sorry
end LearnAugFL.CMP
