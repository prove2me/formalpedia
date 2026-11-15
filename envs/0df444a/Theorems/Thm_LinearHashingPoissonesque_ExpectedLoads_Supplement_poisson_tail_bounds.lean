-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_Supplement_poisson_tail_bounds
-- name    : LinearHashingPoissonesque.ExpectedLoads.Supplement.poisson_tail_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:06:36.860633+00:00
-- url     : https://prove2.me/theorems/4e501c16-7c15-4d7e-9153-6cf3a676084d
-- title:
--   Theorem 9 (companion theorem; not used in the proof of the goal) — Poisson tail bounds
-- statement:
--   Let $u\ge\ell\ge1$, $m\ge1$, $n=2^\ell$, $1\le r\le n$ and $\mu=m/n$. Fix any $S\subseteq\mathbb F_2^u$ of cardinality $m$ and $\varepsilon\in(0,1)$. Under the uniform law on all linear maps $h:\mathbb F_2^u\to\mathbb F_2^\ell$, both bounds hold:
--
--   $$\Pr_h\!\left[L_r^+(S,h)>\mu+T_r^+(m/\varepsilon,n)-\mu/\varepsilon\right]\le\varepsilon,$$
--   $$\Pr_h\!\left[L_r^-(S,h)<\mu-(\mu/\varepsilon-T_r^-(m/\varepsilon,n))\right]\le\varepsilon.$$
--
--   The thresholds use the positive real argument $m/\varepsilon$, without rounding. These bounds govern each extreme-bin average in every ball-to-bin regime, including $r=n$ and the zero branch of the lower threshold.
--
--   Differences from the source:
--   - encoding: binary coordinate spaces and n = 2^ℓ → Fin u → ZMod 2 and Fin ℓ → ZMod 2, with n substituted as 2^ell; reason: these are exactly the source spaces and their cardinalities; ell is independent of the number of balls
--   - encoding: probability under a uniform random linear map → LinMaxLoad.probLin, the average of the event indicator over all linear maps; reason: the finite uniform law includes rank-deficient maps and imposes no surjectivity or affine shift
--   - encoding: averages of the heaviest and lightest r labelled bins → published heaviestAverage and lightestAverage; reason: sorting all bin loads preserves every empty bin and every multiplicity
--   - encoding: Definition 1 real Poisson thresholds → published upperThreshold and lowerThreshold, using their root sets and exact zero branch; reason: on positive real m and 1 ≤ r ≤ n the nonzero root sets are singletons; no rounding or extra hypothesis is imposed
--   - encoding: two displayed tail bounds → a conjunction with real threshold argument (m:ℝ)/eps; reason: all source instances, both tails and their strict events are retained
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.15, Theorem 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf#page=15

import Definitions.Def_LinMaxLoad_probLin
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_PoissonThresholds

namespace LinearHashingPoissonesque.ExpectedLoads.Supplement

/-- Theorem 9, p.15: both tails, with the unrounded real argument m/eps. -/
theorem poisson_tail_bounds {u ell m : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell) (hm : 1 ≤ m)
    (S : Finset (Fin u → ZMod 2)) (hS : S.card = m)
    (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ 2 ^ ell)
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1) :
    let mu : ℝ := (m : ℝ) / (2 : ℝ) ^ ell
    LinMaxLoad.probLin (ZMod 2) (Fin u → ZMod 2) ell
      (fun h => mu + (upperThreshold ((m : ℝ) / eps) (2 ^ ell) r - mu / eps) <
        heaviestAverage S h r) ≤ eps ∧
    LinMaxLoad.probLin (ZMod 2) (Fin u → ZMod 2) ell
      (fun h => lightestAverage S h r <
        mu - (mu / eps - lowerThreshold ((m : ℝ) / eps) (2 ^ ell) r)) ≤ eps := by sorry

end LinearHashingPoissonesque.ExpectedLoads.Supplement
