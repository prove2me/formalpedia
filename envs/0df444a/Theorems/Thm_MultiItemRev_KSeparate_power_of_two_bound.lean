-- Prove2me | Theorems.Thm_MultiItemRev_KSeparate_power_of_two_bound
-- name    : MultiItemRev.KSeparate.power_of_two_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:06.528752+00:00
-- url     : https://prove2.me/theorems/ce0008e3-0186-4014-bd22-c0fdf12ad769
-- title:
--   Proof of Theorem C, p. 26 — power-of-two induction bound
-- statement:
--   Fix $c>0$ for which Proposition 13(ii) holds uniformly, and set $c'=\min\{c,1/2\}$. For each integer $m\ge1$, put $k=2^m$. Every family of $k$ independent nonnegative goods satisfies
--
--   $$\operatorname{Rev}(X_1,\ldots,X_k)\le\frac{\log_2^2 k}{c'}\sum_{i=1}^k\operatorname{Rev}(X_i).$$
--
--   This is the induction estimate inside the paper's proof of Theorem C. **Formalization Note** The hypothesis on $c$ is the full uniform conclusion of Proposition 13(ii); it is not an extra restriction on the distributions in the conclusion.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 26, proof of Theorem C, first paragraph

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KSeparate

theorem power_of_two_bound (c : ℝ) (hcpos : 0 < c)
    (hc : ∀ (k : ℕ), 2 ≤ k →
      ∀ (ν : Fin k → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)],
        ENNReal.ofReal (c / Real.log (k : ℝ)) *
          MultiItemRev.Decomp.BRev (Measure.pi ν) ≤ MultiItemRev.Decomp.SRev (Measure.pi ν))
    (m : ℕ) (hm : 1 ≤ m)
    (ν : Fin (2 ^ m) → Measure ℝ≥0)
    [∀ i, IsProbabilityMeasure (ν i)] :
    MultiItemRev.Decomp.Rev (Measure.pi ν) ≤
      ENNReal.ofReal
          (1 / min c (1 / 2 : ℝ) *
            (Real.logb 2 ((2 ^ m : ℕ) : ℝ)) ^ 2) *
        (∑ i, MultiItemRev.Decomp.Rev1 (ν i)) := by sorry

end MultiItemRev.KSeparate
