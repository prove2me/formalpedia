-- Prove2me | Theorems.Thm_LearnAugFL_CMP_lemma_28
-- name    : LearnAugFL.CMP.lemma_28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:38.153747+00:00
-- url     : https://prove2.me/theorems/a9d90629-92e2-41ed-871c-69c1598df44b
-- title:
--   Lemma 28, p. 24 — moving two points towards each other does not increase their total distance to a third, strictly if not collinear
-- statement:
--   Let $p_1,p_2,p_3$ be three distinct points of the Euclidean plane $\mathbb R^2$ with Euclidean distance $d$, and let $\epsilon\in(0,1)$. Then
--   $$d(p_1,p_3)+d(p_2,p_3)\ \ge\ d\big(p_1+\epsilon(p_2-p_1),p_3\big)+d\big(p_2+\epsilon(p_1-p_2),p_3\big),$$
--   and the inequality is strict when $p_1,p_2,p_3$ are not collinear.
--
--   This convexity fact is what makes clustering two points on a half-axis strictly decrease the optimal cost when the optimum is off the axes (Lemma 15).
-- source:
--   Agrawal, Balkanski, Gkatzelis, Ou & Tan, Learning-Augmented Mechanism Design: Leveraging Predictions for Facility Location, arXiv:2204.01120v1, Lemma 28, p. 24

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

namespace LearnAugFL.CMP

theorem lemma_28 (p₁ p₂ p₃ : Pt) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    dist (p₁ + ε • (p₂ - p₁)) p₃ + dist (p₂ + ε • (p₁ - p₂)) p₃ ≤ dist p₁ p₃ + dist p₂ p₃ ∧
    (¬ Collinear ℝ ({p₁, p₂, p₃} : Set Pt) →
      dist (p₁ + ε • (p₂ - p₁)) p₃ + dist (p₂ + ε • (p₁ - p₂)) p₃ < dist p₁ p₃ + dist p₂ p₃) := by sorry
end LearnAugFL.CMP
