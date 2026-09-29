-- Prove2me | Theorems.Thm_Kawahira_holomorphicIndex_eventuallyEq_of_factor
-- name    : Kawahira.holomorphicIndex_eventuallyEq_of_factor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T21:58:14.52811+00:00
-- url     : https://prove2.me/theorems/832e3fdb-06c9-424a-a2ef-25cfa718e8ef
-- title:
--   Holomorphic index from a simple local factorization
-- statement:
--   Suppose the displacement of a holomorphic map has the local factorization $z-g(z)=(z-a)q(z)$ near $a$, where $q$ is analytic and nonzero at $a$. Then, for every sufficiently small positive radius, the holomorphic fixed-point index around the circle centered at $a$ equals $q(a)^{-1}$. This is the reusable local Cauchy-integral step behind the multiplier formula for simple fixed points.
-- source:
--   T. Kawahira, The Riemann Hypothesis and Holomorphic Index in Complex Dynamics, Experimental Mathematics (2016), https://doi.org/10.1080/10586458.2016.1217443, Proposition 3 and the local Cauchy-integral calculation preceding it.

import Definitions.Def_Kawahira_zeta

open Complex Topology Filter Metric Set

namespace Kawahira

theorem holomorphicIndex_eventuallyEq_of_factor (g q : ℂ → ℂ) (a : ℂ)
    (hq : AnalyticAt ℂ q a) (hqa : q a ≠ 0)
    (hfactor : (fun z => z - g z) =ᶠ[𝓝 a] fun z => (z - a) * q z) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), holomorphicIndex g a r = (q a)⁻¹ := by sorry
