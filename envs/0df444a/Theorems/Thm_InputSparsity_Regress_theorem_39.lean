-- Prove2me | Theorems.Thm_InputSparsity_Regress_theorem_39
-- name    : InputSparsity.Regress.theorem_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T11:02:59.79438+00:00
-- url     : https://prove2.me/theorems/6a67a1c1-ad95-4238-946b-bdd9c2ecf7da
-- title:
--   Theorem 39, p. 25 — affine embedding: S preserves ‖AX − B‖² up to 2ε (weak) and 3ε if it also preserves ‖B̃‖²
-- statement:
--   Let $r\ge1$ and $0<\varepsilon\le1/2$. Let $A\in\mathbb R^{n\times d}$ have rank at most $r$, let $U\in\mathbb R^{n\times k}$ be an orthonormal basis of its column space, let $B\in\mathbb R^{n\times d'}$ and $S\in\mathbb R^{t\times n}$. Let $X^*$ minimize $\|AX-B\|_F^2$ and set $\tilde B=AX^*-B$. Suppose that
--
--   1. $S$ is a subspace embedding for $A$ with parameter $\varepsilon$: $\bigl|\|SAx\|_2^2-\|Ax\|_2^2\bigr|\le\varepsilon\|Ax\|_2^2$ for all $x$;
--   2. $S$ satisfies the approximate matrix multiplication event of Lemma 32 for the pair $(U,\tilde B)$ with error parameter $\varepsilon/\sqrt r$: $\|U^\top S^\top S\tilde B-U^\top\tilde B\|_F^2\le\frac{\varepsilon^2}{r}\|U\|_F^2\|\tilde B\|_F^2$.
--
--   Then for every $X\in\mathbb R^{d\times d'}$,
--   $$\Bigl|\bigl(\|S(AX-B)\|_F^2-\|S\tilde B\|_F^2\bigr)-\bigl(\|AX-B\|_F^2-\|\tilde B\|_F^2\bigr)\Bigr|\le2\varepsilon\,\|AX-B\|_F^2 ,$$
--   so $S$ is an affine embedding with relative error $2\varepsilon$ up to an additive constant (a weak affine embedding). If moreover $\bigl|\|S\tilde B\|_F^2-\|\tilde B\|_F^2\bigr|\le\varepsilon\|\tilde B\|_F^2$, then for every $X$
--   $$\bigl|\|S(AX-B)\|_F^2-\|AX-B\|_F^2\bigr|\le3\varepsilon\,\|AX-B\|_F^2 ,$$
--   which is display (9): $S$ is a $3\varepsilon$-affine embedding.
--
--   Since adding a constant does not change minimizers, the weak form already suffices for sketched optimization; the strong form preserves the objective value itself.
--
--   **Formalization Note** The norms are Frobenius norms (the paper writes $\|\cdot\|$). "$(1\pm2\varepsilon)\|AX-B\|^2-\|\tilde B\|^2$" is read as $\|AX-B\|^2-\|\tilde B\|^2$ up to an error of $2\varepsilon\|AX-B\|^2$, as the proof shows. The subspace embedding is in squared form with parameter $\varepsilon$, as the proof uses it. The Lemma 32 event is for the pair $(U,\tilde B)$, the pair the proof uses after replacing $A$ by an orthonormal basis $U$ of $C(A)$; $\le$ replaces the printed $<$. $\tilde B$ is a named matrix fixed by the hypothesis $\tilde B=AX^*-B$.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 25, Theorem 39 and (9) (proof pp. 25–26)

import Mathlib
import Definitions.Def_InputSparsity_Regress_Basic

namespace InputSparsity.Regress
open Matrix

theorem theorem_39 {n d d' t k : ℕ} (r : ℕ) (A : Matrix (Fin n) (Fin d) ℝ)
    (B : Matrix (Fin n) (Fin d') ℝ) (S : Matrix (Fin t) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ) (ε : ℝ) (Xstar : Matrix (Fin d) (Fin d') ℝ)
    (Btil : Matrix (Fin n) (Fin d') ℝ)
    (hr : 1 ≤ r) (hrank : A.rank ≤ r) (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hU : IsOrthonormalBasisOf U A)
    (hemb : IsSubspaceEmbedding S A ε)
    (hXstar : IsLSMinimizer A B Xstar)
    (hBtil : Btil = A * Xstar - B)
    (hamm : AMMEvent S U Btil (ε / Real.sqrt r)) :
    (∀ X : Matrix (Fin d) (Fin d') ℝ,
      |(InputSparsity.Embed.frobSq (S * (A * X - B)) - InputSparsity.Embed.frobSq (S * Btil)) - (InputSparsity.Embed.frobSq (A * X - B) - InputSparsity.Embed.frobSq Btil)| ≤
        2 * ε * InputSparsity.Embed.frobSq (A * X - B)) ∧
    (|InputSparsity.Embed.frobSq (S * Btil) - InputSparsity.Embed.frobSq Btil| ≤ ε * InputSparsity.Embed.frobSq Btil →
      ∀ X : Matrix (Fin d) (Fin d') ℝ,
        |InputSparsity.Embed.frobSq (S * (A * X - B)) - InputSparsity.Embed.frobSq (A * X - B)| ≤ 3 * ε * InputSparsity.Embed.frobSq (A * X - B)) := by sorry

end InputSparsity.Regress
