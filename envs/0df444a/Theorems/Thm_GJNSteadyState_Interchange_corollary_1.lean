-- Prove2me | Theorems.Thm_GJNSteadyState_Interchange_corollary_1
-- name    : GJNSteadyState.Interchange.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:28.197822+00:00
-- url     : https://prove2.me/theorems/61b17cf9-8b67-4347-80b2-aec0aec555f0
-- title:
--   Corollary 1, p. 18 — the scaled stationary queue lengths Qⁿ(0)/√n are tight
-- statement:
--   Let $\Xi^n$ be the heavy-traffic sequence built from a critically loaded GJN $\Xi$ and $\kappa^0>0$, and let $\pi^n$ be a stationary distribution of $\Xi^n$ for every sufficiently large $n$. If $\bar Q^n(0)=(Q^n(0),\hat a^n(0),\hat v^n(0))\sim\pi^n$, then the sequence of $\mathbb R^J$-valued random vectors
--   $$\big\{Q^n(0)/\sqrt n\big\}_{n\ge1}$$
--   is tight.
--
--   By Prokhorov's theorem the laws $\hat\pi^n$ of $Q^n(0)/\sqrt n$ then have weak limit points, which Theorem 8 identifies.
--
--   **Formalization Note** Tightness is Mathlib's `IsTightMeasureSet` for the set of laws of $Q^n(0)/\sqrt n$. The $\pi^n$ are probability measures on $\mathcal X$ for every $n$ and stationary for all large $n$; finitely many exceptional terms do not affect tightness.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 18, Corollary 1

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Network
import Definitions.Def_GJNSteadyState_Interchange_Dynamics
import Definitions.Def_GJNSteadyState_Interchange_HeavyTraffic
open MeasureTheory Filter Topology Matrix

namespace GJNSteadyState.Interchange

/-- Corollary 1 (p. 18): if `Q̄ⁿ(0) ∼ πⁿ`, a stationary distribution of `Ξⁿ`, then the
`ℝ^J`-valued random vectors `Qⁿ(0)/√n` form a tight sequence. -/
theorem corollary_1 {J : ℕ} (Ξ : Network J) (hΞ : Ξ.IsGJN) (hcrit : IsCritical Ξ)
    (κ0 : Fin J → ℝ) (hκ0 : ∀ j, 0 < κ0 j)
    (π : ℕ → Measure (State J)) [∀ n, IsProbabilityMeasure (π n)]
    (hπ : ∀ᶠ n in atTop, IsStationary (htNet Ξ κ0 n) (π n)) :
    IsTightMeasureSet (Set.range fun n => (π n).map (scaleQ n)) := by sorry

end GJNSteadyState.Interchange
