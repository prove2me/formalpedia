-- Prove2me | Theorems.Thm_Kawahira_logQuotient_hasDerivAt_of_factor
-- name    : Kawahira.logQuotient_hasDerivAt_of_factor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T21:47:34.230238+00:00
-- url     : https://prove2.me/theorems/28171d41-ef73-4d6f-b2ec-2c172ce51b0d
-- title:
--   Reciprocal logarithmic derivative from a local zero factorization
-- statement:
--   Suppose that near $a$ an analytic function factors as $g(z)=(z-a)^m q(z)$, where $m$ is positive, $q$ is analytic at $a$, and $q(a)\ne0$. Then the totalized reciprocal logarithmic derivative $g/g^{\prime}$ vanishes at $a$ and extends differentiably across $a$, with derivative $1/m$. This local factorization interface is reusable for Newton-type maps and other zero-multiplier calculations.
-- source:
--   T. Kawahira, The Riemann Hypothesis and Holomorphic Index in Complex Dynamics, Experimental Mathematics (2016), https://doi.org/10.1080/10586458.2016.1217443, local zero computations underlying Propositions 4 and 13.

import Mathlib

open Complex Topology Filter
namespace Kawahira

theorem logQuotient_hasDerivAt_of_factor (g q : ℂ → ℂ) (a : ℂ) (m : ℕ)
    (hm : 1 ≤ m) (hq : AnalyticAt ℂ q a) (hqa : q a ≠ 0)
    (hgq : g =ᶠ[𝓝 a] fun z => (z - a) ^ m * q z) :
    g a / deriv g a = 0 ∧ HasDerivAt (fun z => g z / deriv g z) (1 / (m : ℂ)) a := by sorry
