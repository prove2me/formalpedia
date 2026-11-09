-- Prove2me | Theorems.Thm_OnlineCarpoolingLei_Oblivious_allowed_move
-- name    : OnlineCarpoolingLei.Oblivious.allowed_move
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:47.101567+00:00
-- url     : https://prove2.me/theorems/1ff25cf7-c207-4c4d-a6fb-7c4a375f2022
-- title:
--   Lemma 5.1 — an allowed move is bounded by the transform $\Psi_g$
-- statement:
--   Let $g:\mathbb R\to[0,\infty)$ be a finite convex function and let $F_g,\kappa_g,\Psi_g$ be as in (5.1). Suppose $\xi\in[-27,27]$ minimizes $\eta\mapsto\max\{g(\eta-2),g(\eta+2)\}$ over $[-27,27]$, the expression defining $\kappa_g$. Then for every real $z$,
--   $$z\ge\xi\implies g(z-2)\le\Psi_g(z),\qquad z\le\xi\implies g(z+2)\le\Psi_g(z).$$
--   Thus at least one move has value at most $\Psi_g(z)$, including the forced move when $|z|>27$: $g(z-2)\le\Psi_g(z)$ when $z>27$, and $g(z+2)\le\Psi_g(z)$ when $z<-27$.
--
--   In the one-dimensional picture $z=\langle x,e\rangle$ and the moves $x\mapsto x\pm e$ change $z$ by $\pm2$; the lemma says that $\Psi_g$ dominates the value of a move that respects the forcing conditions (3.2). It gives the pointwise inequality (6.2) of Lemma 6.1.
--
--   Differences from the source:
--   - encoding: finite convex g : R → [0,∞) → g : ℝ → ℝ with ∀ s, 0 ≤ g s and ConvexOn ℝ Set.univ g; reason: a real-valued function with nonnegative values is exactly a function into [0,∞)
--   - encoding: the minima defining F_g and κ_g in (5.1) → real sInf of the images of [z−2,z+2] and [−27,27]; reason: finite convex functions on R are continuous; these nonempty compact intervals give attained minima, with nonnegative values bounded below
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Lemma 5.1, p.10 (PDF p.10); standing assumption and (5.1) on p.10

import Mathlib
import Definitions.Def_OnlineCarpoolingLei_Oblivious_OneDimTransform

namespace OnlineCarpoolingLei.Oblivious

/-- Lemma 5.1 (p.10). For a finite convex `g : ℝ → [0, ∞)` and any minimizer `ξ ∈ [−27, 27]`
of `η ↦ max {g(η − 2), g(η + 2)}` (the expression defining `κ_g`): `z ≥ ξ ⇒ g(z − 2) ≤ Ψ_g(z)`
and `z ≤ ξ ⇒ g(z + 2) ≤ Ψ_g(z)`. Thus at least one move has value at most `Ψ_g(z)`, including
the forced move when `|z| > 27` (`z − 2` when `z > 27`, `z + 2` when `z < −27`). -/
theorem allowed_move (g : ℝ → ℝ) (hg_nonneg : ∀ s, 0 ≤ g s) (hg_convex : ConvexOn ℝ Set.univ g)
    (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-27 : ℝ) 27)
    (hmin : IsMinOn (fun η => max (g (η - 2)) (g (η + 2))) (Set.Icc (-27 : ℝ) 27) ξ) :
    (∀ z : ℝ, ξ ≤ z → g (z - 2) ≤ psi1 g z) ∧
    (∀ z : ℝ, z ≤ ξ → g (z + 2) ≤ psi1 g z) ∧
    (∀ z : ℝ, g (z - 2) ≤ psi1 g z ∨ g (z + 2) ≤ psi1 g z) ∧
    (∀ z : ℝ, 27 < z → g (z - 2) ≤ psi1 g z) ∧
    (∀ z : ℝ, z < -27 → g (z + 2) ≤ psi1 g z) := by sorry

end OnlineCarpoolingLei.Oblivious
