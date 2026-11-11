-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_bounded_activity_mixing
-- name    : MatchingNearLinear.Glauber.bounded_activity_mixing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:56:38.487471+00:00
-- url     : https://prove2.me/theorems/615fbdac-dfd0-4c34-b26a-56968135b0e2
-- title:
--   Theorem 4.4 — Mixing with bounded edge activities
-- statement:
--   For each fixed $a>0$ there exists $c_a>0$, uniformly over all finite simple graphs with $n$ vertices and $m\ge1$ edges, all real activities $0<\lambda_e\le a$, and all $0<\varepsilon\le1/2$, such that the original single-edge heat-bath chain obeys
--
--   $$t_{\rm mix}(P_{\rm GD},\varepsilon)\le c_a m\log^2(n/\varepsilon).$$
--
--   The constant is independent of the minimum positive activity. The chain chooses uniformly among the original edges and the bound is valid from every matching, including the empty one. This supplies the nonuniform-activity mixing clause of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: finite simple graphs with labeled edge lists → vertices Fin n and edges Fin m with distinct endpoints and injective unordered endpoint map; reason: every finite source graph admits this encoding, including isolated vertices and disconnected graphs
--   - encoding: least nonnegative integer worst-start mixing time bounded by B → existence of a natural horizon t with t ≤ B and total-variation error at most epsilon from every starting state; reason: this is equivalent to the least-time bound and certifies a nonempty set of mixing times
--   - encoding: parameter-uniform or universal big-O bounds → a positive existential constant before all instance parameters; secondary asymptotic clauses quantify fixed bounds first; reason: this is the precise uniform meaning of the source asymptotic notation
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Theorem 4.4, printed p. 21 (PDF p. 23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_MatchingModel

set_option autoImplicit false

namespace MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/

theorem bounded_activity_mixing :
    ∀ a : ℝ, 0 < a → ∃ c : ℝ, 0 < c ∧
    ∀ (n m : ℕ), 1 ≤ m → ∀ (G : Input n m) (lam : Fin m → ℝ),
    ActivityBound lam a → ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
    MixingBound (supportMass (matchingLaw G lam)) (subsetGlauber (matchingLaw G lam)) ε
      (c*m*(Real.log ((n:ℝ)/ε))^2) := by sorry

end MatchingNearLinear.Glauber
