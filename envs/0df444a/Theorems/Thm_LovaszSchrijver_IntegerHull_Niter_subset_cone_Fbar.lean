-- Prove2me | Theorems.Thm_LovaszSchrijver_IntegerHull_Niter_subset_cone_Fbar
-- name    : LovaszSchrijver.IntegerHull.Niter_subset_cone_Fbar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:42:59.536969+00:00
-- url     : https://prove2.me/theorems/d2c0f690-9c51-4ac0-9951-b0d0bc59efdd
-- title:
--   (4) in the proof of Theorem 1.4 — Nᵗ(K) ⊆ cone(K ∩ F̄)
-- statement:
--   Let $K \subseteq Q$ be a closed convex cone in $\mathbb R^{n+1}$. "Consider the unit cube $Q'$ in the hyperplane $x_0 = 0$ [read: $x_0 = 1$] and let $1 \le t \le n$. Consider any face $F$ of $Q'$ of dimension $n - t$ and let $\bar F$ be the union of faces of $Q'$ parallel to $F$." Such a face fixes a set $T$ of $t$ coordinates, so
--   $$\bar F = \{x : x_0 = 1,\ 0 \le x_i \le 1 \ (1 \le i \le n),\ x_i \in \{0, 1\} \ (i \in T)\}.$$
--   Then, for every nonempty set $T$ of $t = |T|$ coordinates,
--   $$N^t(K) \subseteq \operatorname{cone}(K \cap \bar F).$$
--
--   This is the induction claim (4) of the proof of Theorem 1.4: for $t = 1$ it is equivalent to Lemma 1.3, and for $t = n$ it is the nontrivial inclusion $N^n(K) \subseteq K^\circ$ of the theorem.
--
--   **Formalization Note** The page reads "in the hyperplane $x_0 = 0$", a misprint for $x_0 = 1$ (the cube's vertices are the 0–1 vectors with $x_0 = 1$). $\bar F$ is indexed by the set $T$ of fixed coordinates, which is all it depends on; $\operatorname{cone}$ is the span over nonnegative reals. $K$ is assumed closed, which the paper tacitly assumes (polyhedral in all its applications) and which the proof's use of Lemma 1.3 needs.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 172, (4) in the proof of Theorem 1.4 (with Q′, F, F̄ from p. 171)

import Mathlib
import Definitions.Def_LovaszSchrijver_IntegerHull_Basic
import Definitions.Def_LovaszSchrijver_IntegerHull_MatrixCone
open Matrix Pointwise

namespace LovaszSchrijver.IntegerHull

theorem Niter_subset_cone_Fbar {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKQ : K ⊆ Q)
    (T : Finset ι) (hT : T.Nonempty) :
    Niter T.card K ⊆ cone (K ∩ Fbar T) := by sorry

end LovaszSchrijver.IntegerHull
