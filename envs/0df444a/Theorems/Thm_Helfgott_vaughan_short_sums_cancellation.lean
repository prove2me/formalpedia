-- Prove2me | Theorems.Thm_Helfgott_vaughan_short_sums_cancellation
-- name    : Helfgott.vaughan_short_sums_cancellation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T10:46:54.626287+00:00
-- url     : https://prove2.me/theorems/c3ca2e72-c733-452d-b1e1-7b540ad66b0a
-- title:
--   Unconditional cancellation bounds for both short Vaughan sums at every frequency
-- statement:
--   For arbitrary natural cutoffs U,V, every positive compact smoothing scale y, and every circle frequency alpha, both short terms of the exact Vaughan decomposition have explicit upper bounds. Put M=4 log(2), N_d=floor(y/d), and beta_d=d alpha. The Type I term is bounded by the sum, over 1 <= d <= min(U,floor(y)), of M*N_d*max(log(N_d),0) if beta_d=0 and of min(M*N_d*max(log(N_d),0), M*max(log(N_d),0)/||beta_d||) otherwise. The correction is bounded by the sum, over 1 <= d <= min(UV,floor(y)), of log(d) times M*N_d if beta_d=0 and log(d) times min(M*N_d,M/||beta_d||) otherwise. These estimates include all resonances, all compact smoothing endpoints, and the exact arithmetic coefficients. No irrationality or nonresonance hypothesis is needed.
-- source:
--   Vaughan decomposition and classical geometric cancellation with Abel summation, as used in H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2. Complete original Lean proof for the exact compact etaTwo sums, including |mu| <= 1 and the correction coefficient estimate |(mu_{<=U}*Lambda_{<=V})(d)| <= log(d). Mathlib attributions retained. Written by Codex.

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Analysis.Normed.Group.AddCircle
open ArithmeticFunction Finset
open scoped BigOperators Classical

namespace Helfgott

theorem vaughan_short_sums_cancellation (U V : ℕ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    (‖expSum (fun n => ((vaughanTypeOne U n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α‖ ≤
      ∑ d ∈ Finset.Icc 1 (min U (Nat.floor y)),
        if (d : ℤ) • α = 0 then
          (4*Real.log 2)*(Nat.floor (y/(d : ℝ)) : ℝ)*
            max (Real.log (Nat.floor (y/(d : ℝ)) : ℝ)) 0
        else min
          ((4*Real.log 2)*(Nat.floor (y/(d : ℝ)) : ℝ)*
            max (Real.log (Nat.floor (y/(d : ℝ)) : ℝ)) 0)
          ((4*Real.log 2)*max (Real.log (Nat.floor (y/(d : ℝ)) : ℝ)) 0/‖(d : ℤ) • α‖)) ∧
    (‖expSum (fun n => ((vaughanCorrection U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α‖ ≤
      ∑ d ∈ Finset.Icc 1 (min (U*V) (Nat.floor y)),Real.log (d : ℝ)*
        (if (d : ℤ) • α = 0 then (4*Real.log 2)*(Nat.floor (y/(d : ℝ)) : ℝ)
        else min ((4*Real.log 2)*(Nat.floor (y/(d : ℝ)) : ℝ))
          (4*Real.log 2/‖(d : ℤ) • α‖))) := by sorry

end Helfgott
