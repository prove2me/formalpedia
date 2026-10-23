-- Prove2me | Theorems.Thm_LearnAugFL_CMP_lemma_7
-- name    : LearnAugFL.CMP.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:00.516778+00:00
-- url     : https://prove2.me/theorems/7cba95de-72aa-468a-b5a9-937504f089d1
-- title:
--   Lemma 7, p. 13 — the worst case of CMP lies in the Clusters-and-Opt-on-Axes classes
-- statement:
--   Throughout, $\mathbb R^2$ carries the Euclidean distance $d$; $P=(p_1,\dots,p_n)$ is a profile of $n\ge 1$ preferred locations; $c\in[0,1)$ is a confidence parameter with $cn$ an integer; $C^u(f,P)=\frac1n\sum_{i=1}^n d(f,p_i)$ is the utilitarian social cost; $o(P)$ is an optimal (cost-minimizing) location; and $f(P,\hat o,c)$ is the location chosen by the Coordinatewise Median with Predictions (CMP): each coordinate is the lower median of the $n+cn$ values formed by the agents' coordinates and $cn$ copies of the prediction's coordinate. The ratio is $r(P,\hat o,c)=C^u(f(P,\hat o,c),P)/C^u(o(P),P)$.
--
--   Fix $c\in[0,1)$.
--
--   1. (consistency) If $\alpha$ satisfies $r(Q,(0,1),c)\le\alpha$ for every $Q\in\mathcal P^C_{coa}(c)$ (prediction $=o(Q)=(0,1)$), then CMP is $\alpha$-consistent: for every profile $P$ and every optimal location $o$ of $P$,
--   $$C^u(f(P,o,c),P)\le\alpha\,C^u(o,P).$$
--   2. (robustness) If $\beta$ satisfies $r(Q,(0,0),c)\le\beta$ for every $Q\in\mathcal P^R_{coa}(c)$, then CMP is $\beta$-robust: $C^u(f(P,\hat o,c),P)\le\beta\,C^u(o,P)$ for every profile $P$, prediction $\hat o$ and optimal location $o$.
--
--   Lemma 7 reduces the analysis of CMP to one-parameter families of instances; with Lemma 8 it gives Theorem 9.
--
--   **Formalization Note** The optimal location $o(P)$ is taken as any $o$ with `IsOpt P o` (a minimizer of $C^u(\cdot,P)$; it is unique unless the points are collinear). The confidence enters through `Admissible c n k`: $n\ge1$ and $k=cn$ copies of the prediction. Ratios are real quotients `ratio P ô o k`; on every family used here the optimal cost is positive (if all points sat at $o(P)$, CMP would return $o(P)$ because $cn<n$), so no ratio is a junk $0/0$. The page's "$\alpha=\max_{P\in\mathcal P^C_{coa}(c)}r(P,\hat o=o(P),c)$, CMP is $\alpha$-consistent" is stated in implication form (every bound on the class is a bound everywhere), which does not presuppose that the maximum is attained. The proof on p. 22 ends "CMP is $\beta$-consistent", a slip for $\beta$-robust.
-- source:
--   Agrawal, Balkanski, Gkatzelis, Ou & Tan, Learning-Augmented Mechanism Design: Leveraging Predictions for Facility Location, arXiv:2204.01120v1, Lemma 7, p. 13 (proof p. 22)

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

namespace LearnAugFL.CMP

theorem lemma_7 (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∀ α : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt), COA_C c m k' Q →
        ucost Q (cmp Q !₂[0, 1] k') ≤ α * ucost Q !₂[0, 1]) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (o : Pt), IsOpt P o →
        ucost P (cmp P o k) ≤ α * ucost P o) ∧
    (∀ β : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt), COA_R c m k' Q →
        ucost Q (cmp Q 0 k') ≤ β * ucost Q !₂[0, 1]) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (ô o : Pt), IsOpt P o →
        ucost P (cmp P ô k) ≤ β * ucost P o) := by sorry
end LearnAugFL.CMP
