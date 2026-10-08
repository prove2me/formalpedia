-- Prove2me | Theorems.Thm_FracPSG_Subseq_lemma_4_3
-- name    : FracPSG.Subseq.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:59.954355+00:00
-- url     : https://prove2.me/theorems/d9bb48f5-f67d-417d-bd38-f7cfcc2ee3fb
-- title:
--   Lemma 4.3 — subgradient inequality for weakly convex functions
-- statement:
--   Let $S$ be a nonempty closed convex subset of $H=\mathbb R^N$, let $g: H\to\mathbb R$ and $\beta\in\mathbb R$. Suppose that either
--
--   1. $g$ is regular at every point of $S$ and weakly convex with modulus $\beta$ on $S$, or
--   2. $g$ is weakly convex with modulus $\beta$ on an open convex set $O\supseteq S$.
--
--   Then, for all $x,y\in S$ and every limiting subgradient $u\in\partial_L g(x)$,
--   $$\langle u,y-x\rangle\le g(y)-g(x)+\frac\beta2\|y-x\|^2.$$
--
--   The inequality replaces the convex subgradient inequality for the nonconvex denominator $g$; it is the step that controls the term $\theta_n\langle g_n,x_{n+1}-x_n\rangle$ in the descent analysis of the e-PSG algorithm.
--
--   **Formalization Note** $g$ is real-valued; $\partial_L g$ is the limiting subdifferential of $g$ viewed as an extended-real function. Weak convexity "with modulus $\beta$" means that $\beta\ge0$ is a valid constant.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 10, Lemma 4.3

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_FracPSG_Subseq_Basic
import Definitions.Def_FracPSG_Subseq_EPSG

open Filter Topology
open scoped InnerProductSpace

namespace FracPSG.Subseq

open NonconvexSplitting.Shared

/-- Lemma 4.3 (Boţ–Dao–Li, arXiv:2003.04124v2, p. 10), subgradient inequality for weakly convex
functions: if `S` is nonempty closed convex and either `g` is regular and weakly convex with
modulus `β` on `S`, or `g` is weakly convex with modulus `β` on an open convex set `O ⊇ S`, then
`⟨u, y − x⟩ ≤ g(y) − g(x) + (β/2)‖y − x‖²` for all `x, y ∈ S` and `u ∈ ∂_L g(x)`. -/
theorem lemma_4_3 {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {β : ℝ}
    (hSne : S.Nonempty) (hS : IsClosed S) (hSconv : Convex ℝ S)
    (hg : ((∀ x ∈ S, IsRegularAt (fun y => (g y : EReal)) x) ∧ IsWeaklyConvexOn S g β) ∨
      (∃ O, IsOpen O ∧ Convex ℝ O ∧ S ⊆ O ∧ IsWeaklyConvexOn O g β))
    (x y : EuclideanSpace ℝ (Fin N)) (hx : x ∈ S) (hy : y ∈ S)
    (u : EuclideanSpace ℝ (Fin N)) (hu : u ∈ LimitingSubdiff (fun z => (g z : EReal)) x) :
    ⟪u, y - x⟫_ℝ ≤ g y - g x + β / 2 * ‖y - x‖ ^ 2 := by sorry

end FracPSG.Subseq
