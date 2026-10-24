-- Prove2me | Theorems.Thm_LearnAugFL_CMP_lemma_26
-- name    : LearnAugFL.CMP.lemma_26
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:35.455512+00:00
-- url     : https://prove2.me/theorems/c2ba1b57-9570-4414-8b03-7ce7e4365c77
-- title:
--   Lemma 26, p. 23 (Goel–Hann-Caruthers) — moving a point along its ray from the optimum keeps the optimum
-- statement:
--   Throughout, $\mathbb R^2$ carries the Euclidean distance $d$.
--
--   Let $P=(p_1,\dots,p_n)$ be a profile and $o$ an optimal location for the utilitarian cost $C^u(\cdot,P)=\frac1n\sum_j d(\cdot,p_j)$. If $p_i\ne o$ and $p_i'$ lies on the closed ray from $o$ through $p_i$, i.e. $p'_i=o+t(p_i-o)$ for some $t\ge0$, then $o$ is still an optimal location for the profile $(P_{-i},p'_i)$ obtained by replacing $p_i$ with $p'_i$:
--   $$C^u\big(o,(P_{-i},p'_i)\big)\le C^u\big(z,(P_{-i},p'_i)\big)\quad\text{for all } z\in\mathbb R^2.$$
--
--   The lemma is the tool that lets the reduction move points towards (or away from) the optimum while keeping track of it.
--
--   **Formalization Note** The paper writes $o(P_{-i},p'_i)=o(P)$. Since optimal locations need not be unique (collinear profiles), this is read as "$o(P)$ remains an optimal location".
-- source:
--   Agrawal, Balkanski, Gkatzelis, Ou & Tan, Learning-Augmented Mechanism Design: Leveraging Predictions for Facility Location, arXiv:2204.01120v1, Lemma 26 (citing Goel and Hann-Caruthers 2021), p. 23

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

namespace LearnAugFL.CMP

theorem lemma_26 {n : ℕ} (P : Fin n → Pt) (o : Pt) (hP : IsOpt P o) (i : Fin n)
    (hi : P i ≠ o) (t : ℝ) (ht : 0 ≤ t) :
    IsOpt (Function.update P i (o + t • (P i - o))) o := by sorry
end LearnAugFL.CMP
