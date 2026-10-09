-- Prove2me | Theorems.Thm_ModernOnlineLearning_OMD_lemma_6_10_exists
-- name    : ModernOnlineLearning.OMD.lemma_6_10_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:36:36.891327+00:00
-- url     : https://prove2.me/theorems/297a3dd5-8c90-4bcb-920a-d6cdc447dd22
-- title:
--   Lemma 6.10, p. 67 — existence and uniqueness of the OMD update
-- statement:
--   Let $V\subseteq X$ be nonempty, closed, and convex, and assume condition (6.5) or condition (6.6), $V\subseteq\operatorname{int}X$. Let $\psi$ be proper, closed, differentiable on $\operatorname{int}X$, and $\lambda$-strongly convex on $V$, where $\lambda>0$. For any $x\in V\cap\operatorname{int}X$, positive step size $\eta$, and dual vector $g$, there is exactly one $y\in V$ minimizing
--
--   $$z\longmapsto\langle g,z\rangle+\frac{1}{\eta}B_\psi(z;x)\quad(z\in V),$$
--
--   and that point lies in $\operatorname{int}X$. Thus the next OMD iterate exists and is well defined.
--
--   **Formalization Note** The setting also records strict convexity of $\psi$ on $X$ from Definition 6.4. Properness follows from $V\ne\varnothing$ and $V\subseteq X$; closedness is stated through the epigraph. Condition (6.5) is encoded as $\lim_{r\to0^+}\langle\nabla\psi((1-r)x+ry),y-x\rangle=-\infty$ for every $x\in\operatorname{bdry}X$ and $y\in\operatorname{int}X$; the setting assumes (6.5) or (6.6), as the book does.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 6.10, existence and uniqueness clause, p. 67

import Mathlib
import Definitions.Def_ModernOnlineLearning_OMD_Defs

namespace ModernOnlineLearning.OMD

/-- The existence, uniqueness, and interior-point clause of Lemma 6.10, p. 67,
under "(6.5) or (6.6)": the argmin of the update exists, is unique, and lies in
`int X`. -/
theorem lemma_6_10_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X V : Set E) (ψ : E → ℝ) (lam : ℝ)
    (hsetting : IsOMDSetting X V ψ lam)
    (x : E) (hx : x ∈ V ∩ interior X)
    (η : ℝ) (hη : 0 < η) (g : E →L[ℝ] ℝ) :
    (∃! y : E, IsOMDStep V ψ η g x y) ∧
      ∀ y : E, IsOMDStep V ψ η g x y → y ∈ interior X := by sorry

end ModernOnlineLearning.OMD
