-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_JacobiIndex_index_lemma
-- name    : OAI.WeakMTWGlobalSupport.JacobiIndex.index_lemma
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:56:44.614673+00:00
-- url     : https://prove2.me/theorems/5d703130-636f-4849-8b8f-9cc56a28a8cd
-- title:
--   Index lemma: a Jacobi field minimizes the index form
-- statement:
--   **Setting.** $E$ is a real inner product space and $R : \mathbb R \to \mathrm{End}(E)$ is a continuous family of self-adjoint operators: $\langle R_t u, v\rangle = \langle u, R_t v\rangle$. Along a geodesic in a parallel frame, $R_t$ is the curvature operator $u \mapsto \mathcal R(u, \dot\gamma)\dot\gamma$. The index form of fields $U, V : \mathbb R \to E$ is
--   $$I(U, V) = \int_0^1 \bigl(\langle U'(t), V'(t)\rangle - \langle R_t U(t), V(t)\rangle\bigr)\,dt .$$
--   A **Jacobi field** is a solution of $Y'' = -R_t Y$.
--
--   **Statement.** Suppose $I(Z, Z) \ge 0$ for every $C^1$ field $Z$ with $Z(0) = Z(1) = 0$. This is what a minimizing geodesic gives. Let $Y$ be a $C^2$ field that solves the Jacobi equation on $[0, 1]$, and let $X$ be a $C^1$ field with the same endpoint values, $X(0) = Y(0)$ and $X(1) = Y(1)$. Then
--   $$I(Y, Y) \le I(X, X).$$
--
--   This is the classical index lemma of the calculus of variations: under nonnegativity of the index form, a Jacobi field minimizes the index form among fields with its boundary values. The proof writes $X = Y + Z$, uses the Jacobi equation and integration by parts to make the cross term vanish, and applies the hypothesis to $Z$. OpenAI's paper uses it in the proof of its Lemma 2.2. The index form is written out, so the statement uses only Mathlib. Lean: `OAI.WeakMTWGlobalSupport.JacobiIndex.index_lemma`. It is OpenAI's theorem `jacobi_minimizes_index` (in `lean/OAI/Geometry/WeakMTW/Support/FirstCutSupport.lean`), with OpenAI's `indexForm` unfolded.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Support/FirstCutSupport.lean (declaration OAI.WeakMTWGlobalSupport.JacobiIndex.jacobi_minimizes_index)

import Mathlib

open Set Filter MeasureTheory
open scoped Topology

theorem OAI.WeakMTWGlobalSupport.JacobiIndex.index_lemma
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {R : ℝ → E →L[ℝ] E} {Y X : ℝ → E}
    (hR : Continuous R)
    (hsymm : ∀ t u v, inner ℝ (R t u) v = inner ℝ u (R t v))
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 2 Y)
    (hjac : ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv (deriv Y) t = -(R t (Y t)))
    (hstart : X 0 = Y 0) (hend : X 1 = Y 1)
    (hmin : ∀ Z : ℝ → E, ContDiff ℝ 1 Z → Z 0 = 0 → Z 1 = 0 →
      0 ≤ ∫ t in (0 : ℝ)..1, (inner ℝ (deriv Z t) (deriv Z t) - inner ℝ (R t (Z t)) (Z t))) :
    (∫ t in (0 : ℝ)..1, (inner ℝ (deriv Y t) (deriv Y t) - inner ℝ (R t (Y t)) (Y t))) ≤
      ∫ t in (0 : ℝ)..1, (inner ℝ (deriv X t) (deriv X t) - inner ℝ (R t (X t)) (X t)) := by
  sorry
