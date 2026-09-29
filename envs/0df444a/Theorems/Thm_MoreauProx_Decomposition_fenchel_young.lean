-- Prove2me | Theorems.Thm_MoreauProx_Decomposition_fenchel_young
-- name    : MoreauProx.Decomposition.fenchel_young
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:11:00.63224+00:00
-- url     : https://prove2.me/theorems/0253ebee-f068-4be9-bbd0-405e998367f5
-- title:
--   (2.3) — Fenchel–Young inequality f(x) + g(y) ≥ (x | y) for f ∈ Γ₀(H) and its dual g
-- statement:
--   Let $H$ be a real Hilbert space, let $f \in \Gamma_0(H)$ (proper, convex, lower semicontinuous, with values in $]-\infty,+\infty]$), and let $g = f^{*}$ be its dual function, $g(y) = \sup_{x\in H}[(x\mid y) - f(x)]$. Then for all $x, y \in H$,
--   $$ f(x) + g(y) \;\ge\; (x \mid y). $$
--
--   This is the inequality underlying the notion of conjugate points: $x$ and $y$ are called conjugate with respect to $f$ and $g$ exactly when equality holds.
--
--   **Formalization Note** The sum is taken in `EReal`. Because $f$ never takes the value $-\infty$ and is not identically $+\infty$, neither $f(x)$ nor $g(y)$ is $-\infty$, so the convention $-\infty + (+\infty) = -\infty$ never enters.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 277, §2.c, (2.3)

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality

namespace MoreauProx.Decomposition

open scoped InnerProductSpace

/-- Moreau 1965, (2.3), p. 277: for `f ∈ Γ₀(H)` and its dual `g`,
`f(x) + g(y) ≥ (x | y)` for all `x, y`. -/
theorem fenchel_young {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal) (hf : GammaZero f) (x y : H) :
    ((⟪x, y⟫_ℝ : ℝ) : EReal) ≤ f x + conj f y := by sorry

end MoreauProx.Decomposition
