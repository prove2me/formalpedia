-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_poisson_approximation_expectation
-- name    : LinearHashingPoissonesque.ExpectedLoads.poisson_approximation_expectation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T19:03:08.16979+00:00
-- url     : https://prove2.me/theorems/9e41dc51-7707-4494-bfdb-e92d30993953
-- title:
--   Theorem 1 (= Theorem 8) — Poisson approximation in expectation
-- statement:
--   Let $u\ge\ell\ge1$ and $m\ge1$ be integers. Put $n=2^\ell$, let $1\le r\le n$, and fix any set $S\subseteq\mathbb F_2^u$ with $|S|=m$. Sample $h:\mathbb F_2^u\to\mathbb F_2^\ell$ uniformly from all linear maps. The complete expectation comparison is
--
--   $$T_r^-(m,n)\le\mathbb E_h[L_r^-(S,h)]\le\mathbb E_h[L_r^+(S,h)]\le T_r^+(m,n).$$
--
--   Here $L_r^-$ and $L_r^+$ average respectively the lightest and heaviest $r$ bins, with empty bins included, and $T_r^\pm$ are exactly the analytic thresholds of Definition 1. The claim covers every ball/bin regime and every allowed $r$, with no loss in constants. At $r=n$, all four quantities equal $m/n$. This is Theorem 1 on page 4, restated and proved as Theorem 8 on page 15, rather than two different goals.
--
--   Differences from the source:
--   - encoding: binary coordinate spaces, n = 2^ℓ and μ = m/n → Fin u → ZMod 2 and Fin ℓ → ZMod 2, with n and μ substituted in the formulas; reason: these coordinate spaces have exactly the source cardinalities, and ℓ is independent of m
--   - encoding: expectation under the uniform law on all linear maps → LinMaxLoad.avgLin, a finite sum divided by the number of all linear maps; reason: the published definition includes singular maps and introduces no conditioning or regularity assumptions
--   - encoding: the unique real threshold roots of Definition 1, with the lower zero branch at μ ≤ log(n/r) → sInf of each root set and the same explicit lower branch, applied to the real cast of m; reason: sorry-free local proofs establish existence, uniqueness and the root equations throughout the real-m domain; the thresholds are not defined by expected loads
--   - encoding: the complete four-term inequality chain → the conjunction of its three adjacent inequalities; reason: every source conclusion is retained with constant 1
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.4, Theorem 1; restated and proved as Theorem 8, p.15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LogPotential
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_PoissonThresholds

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Theorem 1, p.4, restated and proved as Theorem 8, p.15: the complete chain. -/
theorem poisson_approximation_expectation {u ell m : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell) (hm : 1 ≤ m)
    (S : Finset (Fin u → ZMod 2)) (hS : S.card = m)
    (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ 2 ^ ell) :
    lowerThreshold (m : ℝ) (2 ^ ell) r ≤
      LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => lightestAverage S h r) ∧
    LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => lightestAverage S h r) ≤
      LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => heaviestAverage S h r) ∧
    LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => heaviestAverage S h r) ≤ upperThreshold (m : ℝ) (2 ^ ell) r := by sorry

end LinearHashingPoissonesque.ExpectedLoads
