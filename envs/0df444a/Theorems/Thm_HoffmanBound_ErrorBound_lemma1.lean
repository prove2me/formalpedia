-- Prove2me | Theorems.Thm_HoffmanBound_ErrorBound_lemma1
-- name    : HoffmanBound.ErrorBound.lemma1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:37:12.971677+00:00
-- url     : https://prove2.me/theorems/a494762f-ce9c-4836-ab58-dd8ef32ee14a
-- title:
--   Lemma 1 — there is e > 0 with Fₘ(ȳ) ≦ e Fₘ(y) for every y and every subset S of the rows
-- statement:
--   Let $F_m$ be a positive homogeneous function on $\mathbb R^m$ in the sense of (3). Then there exists $e>0$ such that for every $y=(y_1,\dots,y_m)$ and every subset $S$ of the half spaces (rows) of (1),
--   $$
--   F_m(\bar y)\le e\,F_m(y),\qquad \bar y_i=\begin{cases}y_i & \text{if } i\in S,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   The constant $e$ is uniform in $y$ and $S$. It lets the bound obtained on the active rows pass back to the full residual $(Ax-b)^+$; for the three norms of Section 3, $e=1$.
-- source:
--   Hoffman, On Approximate Solutions of Systems of Linear Inequalities, J. Res. Nat. Bur. Standards 49 (1952), p. 263 (PDF p. 1), Lemma 1

import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model

namespace HoffmanBound.ErrorBound

/-- Hoffman 1952, p. 263, Lemma 1. If `F_m` satisfies (3), there is `e > 0` such that for every
`y` and every subset `S` of the rows, `F_m(ȳ) ≤ e F_m(y)`, where `ȳ` keeps the coordinates of `y`
in `S` and replaces the others by `0`. -/
theorem lemma1 {m : ℕ} (Fm : (Fin m → ℝ) → ℝ) (hFm : IsPosHomogeneous Fm) :
    ∃ e : ℝ, 0 < e ∧ ∀ (y : Fin m → ℝ) (S : Finset (Fin m)), Fm (restrictVec S y) ≤ e * Fm y := by sorry

end HoffmanBound.ErrorBound
