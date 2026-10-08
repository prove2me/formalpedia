-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_current_main_convexity
-- name    : OAI.WeakMTWGlobalSupport.current_main_convexity
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:38.652147+00:00
-- url     : https://prove2.me/theorems/2421f609-331b-4a6c-80b7-e1d23a58daa9
-- statement:
--   The theorem states that, for a dimension n ≥ 2 and a metric space M that is a compact, connected, smooth (C^∞) n-dimensional manifold modeled on Euclidean space ℝⁿ, equipped with a smooth Riemannian bundle structure on its tangent spaces whose induced Riemannian distance is the given metric, the weak Ma–Trudinger–Wang condition HasWeakMTW implies MainConvexity. Here exp(x,v) is the endpoint at time 1 of a complete smooth geodesic through x with initial velocity v, where a geodesic means a smooth curve γ:ℝ→M with γ(0)=x, γ'(0)=v, and that locally around every time t satisfies dist(γ(s),γ(r)) = ‖v‖·|s−r|; if no such endpoint exists, exp(x,v) is set to x. The injectivity domain at x is the set of tangent vectors v for which some a>1 gives dist(x, exp(x,av)) = a‖v‖. With cost(x,y)=dist(x,y)²/2, the quantity mtw(x,v,ξ,η) is −3/2 times the iterated second derivative in t and in s, evaluated at t=s=0, of cost(exp(x,tξ), exp(x,v+sη)). HasWeakMTW asserts that for every point x, every v in the injectivity domain at x, and all tangent vectors ξ and η at x that are orthogonal for the Riemannian inner product, mtw(x,v,ξ,η) ≥ 0. MainConvexity asserts that for every x the injectivity domain at x is a convex subset of the tangent space at x. The theorem is admitted with sorry in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/WeakMTWGlobalSupport.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/WeakMTWGlobalSupport.lean; bytes 2013..2663
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport

namespace OAI

namespace WeakMTWGlobalSupport

open scoped Manifold ContDiff Topology

open Set Filter Manifold Bundle

/-- Weak MTW implies linear convexity of every open tangent injectivity domain. -/
theorem current_main_convexity
    {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [ChartedSpace (WeakMTW.Model n) M]
    [IsManifold (WeakMTW.model n) ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    [RiemannianBundle (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsContMDiffRiemannianBundle (WeakMTW.model n) ∞ (WeakMTW.Model n)
      (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsRiemannianManifold (WeakMTW.model n) M]
    (hmtw : WeakMTW.HasWeakMTW (n := n) (M := M)) :
    WeakMTW.MainConvexity (n := n) (M := M) :=
  by
    sorry

end WeakMTWGlobalSupport
end OAI
