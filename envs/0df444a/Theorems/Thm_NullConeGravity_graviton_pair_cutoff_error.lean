-- Prove2me | Theorems.Thm_NullConeGravity_graviton_pair_cutoff_error
-- name    : NullConeGravity.graviton_pair_cutoff_error
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T19:41:31.649345+00:00
-- url     : https://prove2.me/theorems/33063bdd-2ce3-5a4c-b929-37d68f3a20d1
-- title:
--   Radial cutoff error for the graviton pair amplitude
-- statement:
--   For a real parameter $s>0$, let $A(s)$ be the radial graviton pair amplitude in Eq. (4.33) and let $A_N(s)$ be its sum over physical modes $1,\ldots,N$. For every integer $N\ge1$, the complex amplitude obeys $|A(s)-A_N(s)|\le 1/(2s^2N)$. The first omitted physical mode is $N+1$.
-- source:
--   Quantitative consequence of V. Chandrasekaran, An algebraic quantization of gravity from the null cone, §4.4, Eq. (4.33), https://arxiv.org/html/2611.34924v1#S4.E33. The finite-cutoff inequality here follows from the displayed radial series.

import Definitions.Def_NullConeGravity_pairRadialData

namespace NullConeGravity
theorem graviton_pair_cutoff_error (s : ℝ) (hs : 0 < s) (N : ℕ) (hN : 1 ≤ N) :
    ‖pairAmplitude s - ∑ k ∈ Finset.range N, pairTerm s k‖ ≤
      1 / (2 * s ^ 2 * (N : ℝ)) := by sorry
end NullConeGravity
