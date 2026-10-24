-- Prove2me | Theorems.Thm_LearnAugFL_CMP_lemma_17
-- name    : LearnAugFL.CMP.lemma_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:46.776991+00:00
-- url     : https://prove2.me/theorems/c2c09b49-f15c-4c5f-9a65-e9ab635f585d
-- title:
--   Lemma 17, p. 20 — bounds on the OA and CA families are bounds for all instances
-- statement:
--   Throughout, $\mathbb R^2$ carries the Euclidean distance $d$; $P=(p_1,\dots,p_n)$ is a profile of $n\ge 1$ preferred locations; $c\in[0,1)$ is a confidence parameter with $cn$ an integer; $C^u(f,P)=\frac1n\sum_{i=1}^n d(f,p_i)$ is the utilitarian social cost; $o(P)$ is an optimal (cost-minimizing) location; and $f(P,\hat o,c)$ is the location chosen by the Coordinatewise Median with Predictions (CMP): each coordinate is the lower median of the $n+cn$ values formed by the agents' coordinates and $cn$ copies of the prediction's coordinate. The ratio is $r(P,\hat o,c)=C^u(f(P,\hat o,c),P)/C^u(o(P),P)$.
--
--   Fix $c\in[0,1)$.
--
--   1. (consistency) If $\alpha$ is a real number with $r(Q,o_Q,c)\le\alpha$ for every instance $Q\in\mathcal P^C_{oa}(c)\cup\mathcal P^C_{ca}(c)$, then CMP is $\alpha$-consistent: for every profile $P$ (any $n$ with $cn$ an integer) and every optimal location $o$ of $P$,
--   $$C^u(f(P,o,c),P)\le\alpha\,C^u(o,P).$$
--   2. (robustness) If $\beta$ bounds $r(Q,(0,0),c)$ on $\mathcal P^R_{oa}(c)\cup\mathcal P^R_{ca}(c)$, then CMP is $\beta$-robust: $C^u(f(P,\hat o,c),P)\le\beta\,C^u(o,P)$ for every profile $P$, every prediction $\hat o$ and every optimal $o$.
--
--   The paper states this with $\alpha$ and $\beta$ the maxima of the ratio over the families; it is the first half of the reduction behind Lemma 7.
--
--   **Formalization Note** The optimal location $o(P)$ is taken as any $o$ with `IsOpt P o` (a minimizer of $C^u(\cdot,P)$; it is unique unless the points are collinear). The confidence enters through `Admissible c n k`: $n\ge1$ and $k=cn$ copies of the prediction. Ratios are real quotients `ratio P ô o k`; on every family used here the optimal cost is positive (if all points sat at $o(P)$, CMP would return $o(P)$ because $cn<n$), so no ratio is a junk $0/0$. The page's "$\alpha=\max\dots$, CMP is $\alpha$-consistent" is stated in implication form: every bound valid on the family is valid everywhere. This is equivalent when the maximum exists and does not presuppose that it is attained. Bounds are cross-multiplied.
-- source:
--   Agrawal, Balkanski, Gkatzelis, Ou & Tan, Learning-Augmented Mechanism Design: Leveraging Predictions for Facility Location, arXiv:2204.01120v1, Lemma 17, p. 20 (proof pp. 25–26)

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

namespace LearnAugFL.CMP

theorem lemma_17 (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∀ α : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), (OA_C c m k' Q oQ ∨ CA_C c m k' Q oQ) →
        ucost Q (cmp Q oQ k') ≤ α * ucost Q oQ) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (o : Pt), IsOpt P o →
        ucost P (cmp P o k) ≤ α * ucost P o) ∧
    (∀ β : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), (OA_R c m k' Q oQ ∨ CA_R c m k' Q oQ) →
        ucost Q (cmp Q 0 k') ≤ β * ucost Q oQ) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (ô o : Pt), IsOpt P o →
        ucost P (cmp P ô k) ≤ β * ucost P o) := by sorry
end LearnAugFL.CMP
