-- Prove2me | Theorems.Thm_OptimalAgnosticPAC_Learner_theorem_1
-- name    : OptimalAgnosticPAC.Learner.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:50.457829+00:00
-- url     : https://prove2.me/theorems/73af9459-4d44-49a2-9bf6-f505c8ee058d
-- title:
--   Theorem 1: an optimal agnostic PAC learner
-- statement:
--   Let $\mathcal H$ be a class of measurable classifiers $\mathcal X\to\{-1,+1\}$ with $\mathrm{VC}(\mathcal H)\le d$, $d\ge1$, whose traces depend measurably on the points. There is a deterministic, generally improper learner that uses neither $L^*$ nor $\delta$ and outputs a classifier $\widehat h:\mathcal X\to\{-1,+1\}$, jointly measurable in the sample and the input, such that for every distribution $P$ on $\mathcal X\times\{-1,+1\}$ for which $L^*=\min_{h\in\mathcal H}L(h)$ is attained, every $n\ge1$ and every $0<\delta<1$, with probability at least $1-\delta$ over an i.i.d. sample of size $n$,
--   $$L(\widehat h)\le L^*+2\cdot10^8\Bigl(\sqrt{\frac{L^*(d+\log(48/\delta))}{n}}+\frac{d+\log(48/\delta)}{n}\Bigr).\tag{2}$$
--   Here $\log$ is the natural logarithm.
--
--   Together with the lower bound of Devroye, Györfi and Lugosi, this determines the distribution-free high probability minimax excess risk for binary classification, up to universal constants, at every fixed $L^*$.
--
--   Differences from the source:
--   - encoding: labels in {−1,+1}, inputs in a set X → labels in Bool with true for +1, signed values through sgn, X : Type; reason: the reused vcDim takes Bool-valued functions on a Type; renaming the two labels changes no quantity
--   - generalization: VC(H) = d ≥ 1 → vcDim H ≤ d with d ≥ 1; reason: the bound is increasing in d, so taking d = VC(H) gives the source's statement
--   - reading: footnote 1: all maps depending on the data are measurable → hypotheses that each h ∈ H is measurable and TraceMeasurable H; joint measurability of the learner is a conclusion; reason: the learner is existential, so assuming its measurability would be vacuous; a condition on H makes every trace-based rule measurable
--   - encoding: a deterministic, generally improper learner that uses neither L* nor δ → a function A n S x quantified before P, n and δ, with no membership in H required; reason: a function is deterministic and this quantifier order is what uses neither L* nor δ means
--   - encoding: with probability at least 1 − δ → the sample law (outer measure) of the failure set is bounded by one minus that level; reason: the two agree on measurable events and the failure bound never overstates the probability
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §1, Theorem 1, PDF p. 3 (printed p. 2), with the standing assumptions and footnote 1 on PDF p. 2 (printed p. 1)

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_OptimalAgnosticPAC_Learner_Score
open MeasureTheory
open scoped Classical

namespace OptimalAgnosticPAC.Learner

/-- Theorem 1, PDF p. 3: one deterministic, jointly measurable learner, chosen from `H` and `d`
alone, such that for every distribution with attained `L*`, every `n ≥ 1` and every `0 < δ < 1`,
bound (2) fails with probability at most `δ`. The learner is quantified before `P`, `n` and `δ`,
so it uses neither `L*` nor `δ`; it is not required to output a member of `H`. -/
theorem theorem_1 {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞))
    (hmeas : ∀ h ∈ H, Measurable h) (htrace : TraceMeasurable H) :
    ∃ A : (n : ℕ) → (Fin n → X × Bool) → X → Bool,
      (∀ n : ℕ, Measurable (fun z : (Fin n → X × Bool) × X => A n z.1 z.2)) ∧
      ∀ (P : Measure (X × Bool)) [IsProbabilityMeasure P], AttainsMinRisk P H →
        ∀ n : ℕ, 1 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 →
          sampleLaw P n
            {S | minRisk P H +
                  2 * 10 ^ 8 *
                    (Real.sqrt (minRisk P H * ((d : ℝ) + Real.log (48 / δ)) / (n : ℝ)) +
                      ((d : ℝ) + Real.log (48 / δ)) / (n : ℝ)) <
                risk P (A n S)} ≤
            ENNReal.ofReal δ := by sorry

end OptimalAgnosticPAC.Learner
