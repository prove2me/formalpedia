-- Prove2me | Theorems.Thm_OptInapprox_Bal2Sat_Supplement_theorem_3
-- name    : OptInapprox.Bal2Sat.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:55:23.585199+00:00
-- url     : https://prove2.me/theorems/ea141998-2f54-45a4-99b5-3e928c04a733
-- title:
--   Theorem 3 — UGC hardness above β, including balanced MAX-2SAT
-- statement:
--   Assume the published Unique Games Conjecture. Let
--
--   $$\beta=\min_{\pi/2\le\theta\le\pi}\frac{2+(2/\pi)\theta}{3-\cos\theta}.$$
--
--   For every real approximation factor $r>\beta$, there are real thresholds $c>0$ and $s$ with $s/c<r$ such that distinguishing MAX-2SAT instances of optimum fraction at least $c$ from those of optimum fraction at most $s$ is NP-hard. The same thresholds give NP-hardness even when both kinds of instances are balanced in the published sense of Definition 12. Thus the balanced-instance hardness stated after Theorem 3 is included explicitly.
--
--   The thresholds are chosen after $r$, and reductions may depend on them. Hardness means polynomial-time many-one gap reductions from every NP language, rather than an assumption about algorithms. This is the hardness companion of the referenced balanced MAX-2SAT approximation guarantee.
--
--   Differences from the source:
--   - encoding: weighted MAX-2SAT → unit-weight lists with repeated clauses, embedded into the published Instance; reason: hardness on this encodable subclass implies hardness on the source class; repetitions implement natural weights
--   - encoding: fraction of satisfied weight → the published OPT divided by the positive clause count, with a nonempty list in both promises; reason: the empty instance has no defined normalized objective
--   - reading: NP-hard to approximate within every factor greater than β → for every r>β, some c>0 and s satisfy s/c<r and both general and balanced GapNPHard; reason: §9 gives the completeness and soundness ratios with arbitrarily small errors, and pp.12,21 explicitly retain the balanced restriction
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 12, Theorem 3 and following paragraph; proof pp. 20–21, §9

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Supplement_SatEncoding

namespace OptInapprox.Bal2Sat.Supplement

theorem theorem_3 (hUGC : OptInapprox.MaxCut.UGC) :
    ∀ r : ℝ, beta < r → ∃ c s : ℝ, 0 < c ∧ s / c < r ∧
      SatGapHard false c s ∧ SatGapHard true c s := by sorry

end OptInapprox.Bal2Sat.Supplement
