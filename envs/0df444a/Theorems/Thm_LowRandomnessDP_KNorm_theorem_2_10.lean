-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_theorem_2_10
-- name    : LowRandomnessDP.KNorm.theorem_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:19.769619+00:00
-- url     : https://prove2.me/theorems/fe1574c9-6032-4fb2-abc6-37edf64f9c05
-- title:
--   Theorem 2.10 — optimum countable Knuth–Yao sampler
-- statement:
--   For every probability distribution $p$ on a finite or countably infinite alphabet, there exists a prefix-free fair-bit decision tree $T$ with exact output law $p$ that attains the minimum expected bit count among all such trees, and
--
--   $$\mathbb E[L_T]\le H_2(p)+2.$$
--
--   The inequality and optimality use extended nonnegative expectations and include infinite entropy. The tree terminates almost surely and may have infinitely many leaves and unbounded depth. This turns the entropy target into an operational exact-sampling target.
--
--   Differences from the source:
--   - encoding: a finite or infinite discrete probability distribution and optimum DDG-tree → a countable PMF and a mass-one prefix-free leaf family minimizing extended expected depth; reason: the leaf cylinders are exactly fresh fair-bit trajectories and the extended domain includes infinite entropy; no computability restriction is introduced
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, Theorem 2.10, PDF page 8 / printed page 6

import Definitions.Def_LowRandomnessDP_KNorm_Sampling

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace LowRandomnessDP.KNorm

theorem theorem_2_10 {ι : Type} [Countable ι] (p : PMF ι) :
    ∃ T : DDG ι, T.law = p ∧ T.expectedBits ≤ entropyBits p + 2 ∧
      ∀ U : DDG ι, U.law = p → T.expectedBits ≤ U.expectedBits := by sorry

end LowRandomnessDP.KNorm
