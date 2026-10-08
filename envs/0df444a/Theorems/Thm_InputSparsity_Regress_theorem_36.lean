-- Prove2me | Theorems.Thm_InputSparsity_Regress_theorem_36
-- name    : InputSparsity.Regress.theorem_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T11:03:05.552533+00:00
-- url     : https://prove2.me/theorems/7791ace7-290b-4b13-a094-7ce055bb7806
-- title:
--   Theorem 36, p. 24 — sketched multiple-response regression: ‖AỸ − B‖_F² ≤ (1 + 4ε)‖AY* − B‖_F²
-- statement:
--   Let $r\ge1$ and $\varepsilon>0$. Let $A\in\mathbb R^{n\times d}$ have rank at most $r$, let $U\in\mathbb R^{n\times k}$ be an orthonormal basis of the column space $C(A)$, let $B\in\mathbb R^{n\times d'}$, and let $S\in\mathbb R^{t\times n}$ be a fixed matrix. Let $Y^*$ be any solution of
--   $$\min_Y\|AY-B\|_F^2\qquad(8)$$
--   and suppose that
--
--   1. $S$ is a subspace embedding for $A$ with parameter $\eta\in[0,1/2]$: $\bigl|\|SAx\|_2^2-\|Ax\|_2^2\bigr|\le\eta\|Ax\|_2^2$ for every $x\in\mathbb R^d$;
--   2. $S$ satisfies the approximate matrix multiplication event of Lemma 32 for the pair $(U,\,B-AY^*)$ with error parameter $\sqrt{\varepsilon/r}$:
--   $$\|U^\top S^\top S(B-AY^*)-U^\top(B-AY^*)\|_F^2\le\frac{\varepsilon}{r}\,\|U\|_F^2\,\|B-AY^*\|_F^2 .$$
--
--   Then every solution $\tilde Y$ of the sketched problem
--   $$\min_Y\|S(AY-B)\|_F^2\qquad(7)$$
--   satisfies
--   $$\|A\tilde Y-B\|_F^2\le(1+4\varepsilon)\,\|AY^*-B\|_F^2 .$$
--   Taking square roots, $\|A\tilde Y-B\|_F\le\sqrt{1+4\varepsilon}\,\|AY^*-B\|_F\le(1+2\varepsilon)\|AY^*-B\|_F$, which is the paper's $(1+\epsilon)$ guarantee after rescaling $\varepsilon$ by a constant factor.
--
--   This is the sketch-and-solve principle for regression: solving the small problem $\min_Y\|SAY-SB\|_F$ gives a near-optimal solution of the original problem whenever $S$ embeds $C(A)$ and approximates the products $U^\top(B-AY^*)$. It underlies the paper's input-sparsity-time regression and low-rank approximation algorithms, where random sketches satisfy both conditions with constant probability.
--
--   **Formalization Note** The statement is deterministic: $S$ is any matrix satisfying the two conditions. The conclusion is the squared bound with the explicit constant $4$ that the proof derives; the printed "$\|A\tilde Y-B\|_F\le(1+\epsilon)\|AY^*-B\|_F$" holds only after a rescaling of $\epsilon$ that the paper leaves unspecified. $\eta$ plays the role of the paper's $\epsilon_0^2$ ($\epsilon_0\le1/\sqrt2\iff\eta\le1/2$), as in the proof of Lemma 37 (p. 37). "$S$ satisfies Lemma 32" is read as the event for the pair $(U,B-AY^*)$ that the proof uses (p. 37), with $\le$ for the printed $<$. $\tilde Y$ and $Y^*$ are arbitrary minimizers, since "the solution" need not be unique. $r\ge1$ makes $\varepsilon/r$ meaningful; the paper's "$n>d$" concerns running times and is not assumed.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 24, Theorem 36, (7), (8) and its proof

import Mathlib
import Definitions.Def_InputSparsity_Regress_Basic

namespace InputSparsity.Regress
open Matrix

theorem theorem_36 {n d d' t k : ℕ} (r : ℕ) (A : Matrix (Fin n) (Fin d) ℝ)
    (B : Matrix (Fin n) (Fin d') ℝ) (S : Matrix (Fin t) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ) (ε η : ℝ) (Ystar Ytil : Matrix (Fin d) (Fin d') ℝ)
    (hr : 1 ≤ r) (hrank : A.rank ≤ r)
    (hε : 0 < ε) (hη₀ : 0 ≤ η) (hη : η ≤ 1 / 2)
    (hU : IsOrthonormalBasisOf U A)
    (hemb : IsSubspaceEmbedding S A η)
    (hYstar : IsLSMinimizer A B Ystar)
    (hamm : AMMEvent S U (B - A * Ystar) (Real.sqrt (ε / r)))
    (hYtil : IsSketchedMinimizer S A B Ytil) :
    InputSparsity.Embed.frobSq (A * Ytil - B) ≤ (1 + 4 * ε) * InputSparsity.Embed.frobSq (A * Ystar - B) := by sorry

end InputSparsity.Regress
