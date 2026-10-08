-- Prove2me | Theorems.Thm_LemkeLCP_Existence_lemma_2_p4
-- name    : LemkeLCP.Existence.lemma_2_p4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:04:00.770983+00:00
-- url     : https://prove2.me/theorems/b7672de7-abc0-446e-be17-71826a2e1c0d
-- title:
--   Lemma 2 (p. 4) — Z is empty iff some u ≥ 0 has Mᵀu ≤ 0 and uᵀq > 0
-- statement:
--   Let $M$ be a real square matrix of order $n$, $q\in\mathbb R^n$, and $Z=\{z\ge0 : Mz-q\ge0\}$. Then $Z$ is empty if and only if there is a vector $u\ge 0$ satisfying
--   $$M^{\mathsf T}u\le 0\qquad\text{and}\qquad u^{\mathsf T}q>0. \tag{5}$$
--
--   This is a theorem of the alternative of Farkas type. In the proof of Theorem 4 only the direction "a $u$ satisfying (5) makes $Z$ empty" is used: it is how the case $\bar z_0>0$ of the augmented path is shown to certify infeasibility. The page states it as an equivalence, and so does this item.
--
--   **Formalization Note** It is the specialization of part (ii) of the published Farkas lemma `MatousekLP.Duality.farkas_three_variants` to $A=-M$, $b=-q$, over a general finite index type. The paper labels two different results "Lemma 2" (pp. 4 and 6); this is the one on p. 4, which the proof of Theorem 4 on p. 8 calls "Lemma 1".
-- source:
--   Lemke, Bimatrix equilibrium points and mathematical programming, hal-01885823v1, p. 4, Lemma 2, (5)

import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix

namespace LemkeLCP.Existence

theorem lemma_2_p4 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ) :
    Z M q = ∅ ↔ ∃ u : ι → ℝ, 0 ≤ u ∧ Mᵀ *ᵥ u ≤ 0 ∧ 0 < u ⬝ᵥ q := by sorry

end LemkeLCP.Existence
