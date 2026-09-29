-- Prove2me | Theorems.Thm_KServer_workFnU_dual_pair_exchange
-- name    : KServer.workFnU_dual_pair_exchange
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T06:54:01.186657+00:00
-- url     : https://prove2.me/theorems/cbcad3d7-557d-4cfe-a8b8-6393171cd16b
-- title:
--   The greedy exchange for the dual pair functional
-- statement:
--   Fix two points $x_2, x_3$ of a $3$-server instance and consider, over pairs of points, the **dual pair functional**
--
--   $$F(u,v) \;=\; w(x_3, u, v) - d(u, x_2) - d(v, x_2),$$
--
--   with $w$ the (unlabelled) work function. Suppose $x_1$ minimises the constrained functional $u \mapsto F(u, x_2)$ --- pairs containing $x_2$ --- and $(p,q)$ minimises $F$ outright. Then $F$ attains its global minimum at a pair **containing $x_1$**: there is $w'$ with $F(x_1, w') \le F(u,v)$ for all $u, v$.
--
--   ## Role
--
--   This is the greedy exchange that drives Lemma 25 of Coester and Koutsoupias, the anchor-selection lemma of their tree analysis. There, $x_1$ is chosen to minimise $u \mapsto w(u\,x_2 x_3) - d(u,x_2)$, and the potential summand $w(\bar x_2 \bar x_2 x_3)$ --- which, by the coordinate-local envelope, is $4\Delta$ plus the global minimum of $F$ --- must be shown to resolve *to that same $x_1$*. The exchange provides exactly this: the global dual minimum is attained with $x_1$ in one slot, whence the resolution $w(\bar x_2 \bar x_2 x_3) = w(x_1 \bar x_2 x_3) + d(x_1, \bar x_2)$ follows by two Lipschitz collapses. The paper cites its general greedy lemma (quasi-convex exchange à la Dress--Wenzel) for this step; at pair level a single application of quasiconvexity suffices.
--
--   ## About the proof
--
--   Quasiconvexity of the work function in its three-point form, with $x_3$ as the common coordinate, aligns the pairs $(x_1, x_2)$ and $(p,q)$: one of the two pairings $(x_1,p),(x_2,q)$ or $(x_1,q),(x_2,p)$ has value-sum at most $F$-sum of the originals (the subtracted distance terms cancel exactly across any pairing, since each of $x_1, x_2, p, q$ appears exactly once on each side). In either pairing, the hybrid containing $x_2$ is bounded below by the constrained minimality of $x_1$, leaving the hybrid containing $x_1$ below the global minimum --- so it *is* a global minimum, with witness $p$ or $q$ accordingly. No finiteness, no tree structure, and no attainment assumptions beyond the two hypothesised minimisers are used.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture', ICALP 2021, arXiv:2102.10474, proof of Lemma 25 (lem:treeSwapx12): the application of the greedy lemma (their Lemma 13) to X ↦ w(X) − d(X, x₂²); here derived at pair level from a single quasiconvex exchange.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_dual_pair_exchange (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (x₂ x₃ x₁ p q : M)
    (hx₁ : ∀ u : M, workFnU C₀ σ ![x₃, x₁, x₂] - dist x₁ x₂
        ≤ workFnU C₀ σ ![x₃, u, x₂] - dist u x₂)
    (hpq : ∀ u v : M, workFnU C₀ σ ![x₃, p, q] - dist p x₂ - dist q x₂
        ≤ workFnU C₀ σ ![x₃, u, v] - dist u x₂ - dist v x₂) :
    ∃ w : M, ∀ u v : M,
      workFnU C₀ σ ![x₃, x₁, w] - dist x₁ x₂ - dist w x₂
        ≤ workFnU C₀ σ ![x₃, u, v] - dist u x₂ - dist v x₂ := by sorry

end KServer
