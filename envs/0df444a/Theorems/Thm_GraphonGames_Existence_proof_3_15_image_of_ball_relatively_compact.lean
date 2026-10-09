-- Prove2me | Theorems.Thm_GraphonGames_Existence_proof_3_15_image_of_ball_relatively_compact
-- name    : GraphonGames.Existence.proof_3_15_image_of_ball_relatively_compact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:27.736069+00:00
-- url     : https://prove2.me/theorems/1c29d287-d17e-4695-a083-44a403554287
-- title:
--   Proof of Theorem 3.15, p. 15 — W(B_χ) is a relatively compact subset of L²(I)
-- statement:
--   Let $w$ be a graphon with integral operator $\mathbf W$ and let $\chi\in\mathbb R$. The image under $\mathbf W$ of the closed ball $B_\chi=\{g\in L^2(I):\|g\|_{L^2(I)}\le\chi\}$ is relatively compact in $L^2(I)$:
--   $$\overline{\mathbf W(B_\chi)}\ \text{is compact in }L^2(I).$$
--
--   This is the second claim of the proof of Theorem 3.15, which the paper justifies by $\mathbf W$ being Hilbert–Schmidt, hence compact.
--
--   **Formalization Note.** The set $\mathbf W(B_\chi)$ is taken in Mathlib's `Lp ℝ 2` and described through representatives: the classes $F$ with $F=\mathbf Wg$ a.e. for some $g\in L^2(I)$ with $\|g\|\le\chi$. For $\chi<0$ the radius is clipped to $0$ and the set is $\{0\}$; the claim is then trivially true, as it is for the paper's empty ball.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 15, proof of Theorem 3.15, third sentence

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting

open MeasureTheory
open scoped ENNReal

namespace GraphonGames.Existence

theorem proof_3_15_image_of_ball_relatively_compact (w : I → I → ℝ) (hw : IsGraphon w) (χ : ℝ) :
    IsCompact (closure {F : Lp ℝ 2 (volume : Measure I) | ∃ g : I → ℝ, MemLp g 2 volume ∧
      eLpNorm g 2 volume ≤ ENNReal.ofReal χ ∧ (F : I → ℝ) =ᵐ[volume] graphonApply w g}) := by sorry

end GraphonGames.Existence
