-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_lemma_6_4
-- name    : ListReplicableBias.LowerBound.Supplement.lemma_6_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T20:26:29.679837+00:00
-- url     : https://prove2.me/theorems/f8f24910-2477-4f80-a0d2-b98e6158bcad
-- title:
--   Lemma 6.4 — three facts about good shifts
-- statement:
--   Let $u\in[0,\varepsilon)$, $\alpha>0$ and $p,\hat p\in[0,1]$ with $|\hat p-p|\le\alpha$.
--   1. If $u$ is $\alpha$-good for $p$, then $R_u(x)=R_u(y)$ for all $x,y\in[p-\alpha,p+\alpha)$.
--   2. If $u$ is $3\alpha$-good for $p$, then $u$ is $2\alpha$-good for $\hat p$.
--   3. If $u$ is $2\alpha$-good for $\hat p$, then $R_u(p)=R_u(\hat p)$.
--
--   These facts make the rounding of an accurate empirical mean coincide with the rounding of the true bias, which is the source of replicability in Algorithm 1 (Lemma 6.11).
--
--   Differences from the source: none.
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Lemma 6.4, PDF p. 8

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Rounding

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Lemma 6.4, PDF p. 8, all three clauses. -/
theorem lemma_6_4 (ε u α p phat : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) ε) (hα : 0 < α)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hphat : phat ∈ Set.Icc (0 : ℝ) 1)
    (hclose : |phat - p| ≤ α) :
    (IsGoodShift ε α p u →
      ∀ x ∈ Set.Ico (p - α) (p + α), ∀ y ∈ Set.Ico (p - α) (p + α),
        roundShift ε u x = roundShift ε u y) ∧
    (IsGoodShift ε (3 * α) p u → IsGoodShift ε (2 * α) phat u) ∧
    (IsGoodShift ε (2 * α) phat u → roundShift ε u p = roundShift ε u phat) := by sorry

end ListReplicableBias.LowerBound.Supplement
