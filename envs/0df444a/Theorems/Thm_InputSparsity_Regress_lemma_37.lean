-- Prove2me | Theorems.Thm_InputSparsity_Regress_lemma_37
-- name    : InputSparsity.Regress.lemma_37
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T11:03:00.539586+00:00
-- url     : https://prove2.me/theorems/6e905035-402b-44d1-ac12-8b026d0ec6bb
-- title:
--   Lemma 37, p. 24 — for A with orthonormal columns, ‖A(Ỹ − Y*)‖_F ≤ 2√ε‖B − AY*‖_F
-- statement:
--   Let $r\ge1$ and $\varepsilon>0$. Let $A\in\mathbb R^{n\times k}$ have orthonormal columns ($A^\top A=I_k$) with $k\le r$, let $B\in\mathbb R^{n\times d'}$, and let $S\in\mathbb R^{t\times n}$. Suppose that
--
--   1. $S$ is a subspace embedding for $A$ with parameter $\eta\in[0,1/2]$: $\bigl|\|SAx\|_2^2-\|Ax\|_2^2\bigr|\le\eta\|Ax\|_2^2$ for all $x$;
--   2. $Y^*$ minimizes $\|AY-B\|_F^2$;
--   3. $S$ satisfies the approximate matrix multiplication event of Lemma 32 for the pair $(A,\,B-AY^*)$ with error parameter $\sqrt{\varepsilon/r}$: $\|A^\top S^\top S(B-AY^*)-A^\top(B-AY^*)\|_F^2\le\frac{\varepsilon}{r}\|A\|_F^2\|B-AY^*\|_F^2$;
--   4. $\tilde Y$ minimizes $\|S(AY-B)\|_F^2$.
--
--   Then
--   $$\|A(\tilde Y-Y^*)\|_F\le2\sqrt\varepsilon\,\|B-AY^*\|_F .$$
--
--   This is the core estimate of the sketch-and-solve analysis: the sketched solution is close to the true one in the geometry of $A$.
--
--   **Formalization Note** "For $S,A,B,Y^*$ and $\tilde Y$ as in Theorem 36" is spelled out. With orthonormal columns $\operatorname{rank}A=k$, so "rank at most $r$" is $k\le r$. The embedding parameter $\eta$ plays the role of the paper's $\epsilon_0^2$, and $\epsilon_0\le1/\sqrt2$ becomes $\eta\le1/2$: the proof (Appendix A, p. 37) bounds $\|A^\top S^\top SA-I\|_2$ by $\epsilon_0^2$ and uses $\epsilon_0^2\le1/2$; under the norm convention $\|SAx\|_2=(1\pm\epsilon_0)\|Ax\|_2$ of §1.2 with $\epsilon_0=1/\sqrt2$ the constant $2$ would fail. The Lemma 32 event is the inequality it is used as in the proof (p. 37), with $\le$ for the printed $<$.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 24, Lemma 37 (proof in Appendix A, p. 37)

import Mathlib
import Definitions.Def_InputSparsity_Regress_Basic

namespace InputSparsity.Regress
open Matrix

theorem lemma_37 {n k d' t : ℕ} (r : ℕ) (A : Matrix (Fin n) (Fin k) ℝ)
    (B : Matrix (Fin n) (Fin d') ℝ) (S : Matrix (Fin t) (Fin n) ℝ) (ε η : ℝ)
    (Ystar Ytil : Matrix (Fin k) (Fin d') ℝ)
    (hr : 1 ≤ r) (hA : InputSparsity.Embed.HasOrthonormalCols A) (hk : k ≤ r)
    (hε : 0 < ε) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hemb : IsSubspaceEmbedding S A η)
    (hYstar : IsLSMinimizer A B Ystar)
    (hamm : AMMEvent S A (B - A * Ystar) (Real.sqrt (ε / r)))
    (hYtil : IsSketchedMinimizer S A B Ytil) :
    Real.sqrt (InputSparsity.Embed.frobSq (A * (Ytil - Ystar))) ≤
      2 * Real.sqrt ε * Real.sqrt (InputSparsity.Embed.frobSq (B - A * Ystar)) := by sorry

end InputSparsity.Regress
