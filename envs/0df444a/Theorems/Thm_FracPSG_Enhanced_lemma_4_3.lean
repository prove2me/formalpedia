-- Prove2me | Theorems.Thm_FracPSG_Enhanced_lemma_4_3
-- name    : FracPSG.Enhanced.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:25.571054+00:00
-- url     : https://prove2.me/theorems/143b4e61-d5ea-4742-acb5-caa7cae74378
-- title:
--   Lemma 4.3 — subgradient inequality for weakly convex functions
-- statement:
--   Let $S$ be a nonempty closed convex subset of a finite-dimensional real Hilbert space $H$, let $g: H\to\mathbb R$ and $\beta\ge0$, and suppose that either $g$ is regular at every point of $S$ and weakly convex with modulus $\beta$ on $S$, or $g$ is weakly convex with modulus $\beta$ on an open convex set $O$ containing $S$ (weak convexity on a convex set $C$ with modulus $\beta$ meaning that $g+\frac\beta2\|\cdot\|^2$ is convex on $C$). Then for all $x,y\in S$ and every limiting subgradient $u\in\partial_L g(x)$,
--   $$\langle u,\,y-x\rangle\ \le\ g(y)-g(x)+\frac\beta2\|y-x\|^2 .$$
--
--   In the proof of Theorem 6.1 it is applied, in inequality (31), to each piece $g_i$ of the max-type denominator, which is continuously differentiable near $S$ and so regular with $\partial_L g_i(x)=\{\nabla g_i(x)\}$.
--
--   **Formalization Note** $H$ is `EuclideanSpace ℝ (Fin N)` and $g$ is real-valued. Regularity at $x$ is equality of the Fréchet and limiting subdifferentials there; "modulus $\beta$" is read as "a valid constant $\beta\ge0$", not necessarily the smallest one.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 10, Lemma 4.3

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_FracPSG_Enhanced_Basic

open Filter Topology
open scoped InnerProductSpace

namespace FracPSG.Enhanced

open NonconvexSplitting.Shared

/-- Lemma 4.3 (Boţ–Dao–Li, arXiv:2003.04124v2, p. 10), subgradient inequality for weakly convex
functions: let `S` be a nonempty closed convex set and suppose that either `g` is regular (at every
point of `S`) and weakly convex with modulus `β` on `S`, or `g` is weakly convex with modulus `β`
on an open convex set `O ⊇ S`. Then for all `x, y ∈ S` and `u ∈ ∂_L g(x)`,
`⟨u, y − x⟩ ≤ g(y) − g(x) + (β/2)‖y − x‖²`. -/
theorem lemma_4_3 {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {β : ℝ}
    (hSne : S.Nonempty) (hS : IsClosed S) (hSconv : Convex ℝ S)
    (hg : ((∀ x ∈ S, FracPSG.Subseq.IsRegularAt (fun y => (g y : EReal)) x) ∧
        FracPSG.Subseq.IsWeaklyConvexOn S g β) ∨
      (∃ O, IsOpen O ∧ Convex ℝ O ∧ S ⊆ O ∧ FracPSG.Subseq.IsWeaklyConvexOn O g β))
    (x y : EuclideanSpace ℝ (Fin N)) (hx : x ∈ S) (hy : y ∈ S)
    (u : EuclideanSpace ℝ (Fin N)) (hu : u ∈ LimitingSubdiff (fun z => (g z : EReal)) x) :
    ⟪u, y - x⟫_ℝ ≤ g y - g x + β / 2 * ‖y - x‖ ^ 2 := by sorry

end FracPSG.Enhanced
