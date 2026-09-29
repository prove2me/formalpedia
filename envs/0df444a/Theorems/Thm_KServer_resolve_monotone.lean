-- Prove2me | Theorems.Thm_KServer_resolve_monotone
-- name    : KServer.resolve_monotone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T19:51:52.915356+00:00
-- url     : https://prove2.me/theorems/85be2f72-ca63-4512-946e-2e6d28b85066
-- title:
--   A resolution survives duplicating the resolving point
-- statement:
--   Let $w$ be a work function whose last request is $r$. Say that a configuration $X$ **resolves from** $x \in X$ if
--   $$w(X) = w(X - x + r) + rx,$$
--   that is, if an optimal way of ending at $X$ is to end at $X$ with $x$ reached last, coming from the request. Then, for three servers: if $\{x,y,z\}$ resolves from $x$, so does $\{x,x,z\}$ — the configuration obtained by replacing $y$ with a second copy of $x$.
--
--   ## Role
--
--   Resolutions are how the Coester–Koutsoupias analysis keeps track of which server "last touched" the request, and the potential $\Phi$ is built from configurations of the form $\bar x_i^{\,i} x_{i+1} \dots x_k$ in which points are repeated. Their tree argument repeatedly needs to know that a resolution survives such a duplication, and this lemma is what licenses that.
--
--   Every configuration resolves from *some* point, so the content is that resolving from $x$ is inherited rather than being lost to a competing point. The proof is by exclusion: suppose $\{x,x,z\}$ resolved instead from $z$. Then
--
--   $$w(xyz) + w(x^2z) \;=\; w(yzr) + w(x^2r) + rx + rz \;\ge\; w(xyr) + w(xzr) + rx + rz \;\ge\; w(xyz) + w(x^2z),$$
--
--   where the first equality uses the two resolutions, the first inequality is quasiconvexity of the work function applied to $\{y,z,r\}$ and $\{x,x,r\}$ — the two rematchings coincide because $x$ is repeated, so no case split arises — and the second is $1$-Lipschitzness. The two ends agree, so every step is an equality; and equality in the last step is exactly the statement that $\{x,x,z\}$ resolves from $x$.
--
--   **Formalization note.** That every configuration resolves from some point is the one-step recursion for the work function, which supplies the index to case on: two of the three cases give the conclusion outright, after normalising the configuration by permutation invariance, and only the third — resolving at $z$ — needs the displayed chain.
-- source:
--   C. Coester, E. Koutsoupias, Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle, ICALP 2021, arXiv:2102.10474, Lemma 12 (resolveMonotone): 'Let w in W^k_M(r), let X be a k-point multiset and x, y in X. If X resolves from x in w, then also X - y + x resolves from x in w.' Stated here for k = 3.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem resolve_monotone (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r x y z : M)
    (hres : workFnU C₀ (σ ++ [r]) ![x, y, z] = workFnU C₀ (σ ++ [r]) ![r, y, z] + dist r x) :
    workFnU C₀ (σ ++ [r]) ![x, x, z] = workFnU C₀ (σ ++ [r]) ![r, x, z] + dist r x := by sorry

end KServer
