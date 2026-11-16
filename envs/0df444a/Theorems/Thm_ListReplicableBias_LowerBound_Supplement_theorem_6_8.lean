-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_theorem_6_8
-- name    : ListReplicableBias.LowerBound.Supplement.theorem_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:26:02.316207+00:00
-- url     : https://prove2.me/theorems/a050812d-cf97-44de-ad88-c78af4e7badd
-- title:
--   Theorem 6.8 (= Thm 4.3) (corrected: δ replaced by min(δ, 1/2) inside the bound) — a (d+1)-list replicable estimator with O((d²/ε²) log(d/δ) log(1/δ)) samples
-- statement:
--   There is an absolute constant $C>0$ such that for every $d\in\mathbb N$ and all $\varepsilon,\delta\in(0,1)$ there is a randomized $N$-toss sampling algorithm on $d$ coins that is $(d+1,\varepsilon,\delta)$-list replicable for the $d$-CoinBiasEstimationProblem and uses
--   $$N\le C\,\frac{d^2}{\varepsilon^2}\,\ln\frac{d}{\delta'}\,\ln\frac1{\delta'},\qquad \delta'=\min(\delta,1/2),$$
--   samples. For $\delta\le1/2$ this is exactly the printed bound $O\big(\frac{d^2}{\varepsilon^2}\log\frac d\delta\log\frac1\delta\big)$.
--
--   This upper bound matches the lower bound of the mission's goal (Theorem B.1) up to polylogarithmic factors, improving the cubic dependence on $d$ of earlier $(d+1)$-list replicable algorithms.
--
--   Differences from the source:
--   - correction: N = O((d²/ε²) log(d/δ) log(1/δ)) for every δ ∈ (0, 1) with one constant → the bound with δ' = min(δ, 1/2) in place of δ; reason: false as δ → 1: for d = 3, ε < 1/(267C) and δ = 1 − η with 27ε³ < η < ε²/(10C) the bound is < 1, forcing N = 0, but a zero-toss algorithm has one output law, which cannot put mass ≥ η on each of ≥ (1/(3ε))³ disjoint closed ε-balls around grid points 3ε apart (total mass ≥ η/(27ε³) > 1); the paper's proof (Appendix A.2) assumes δ < 1/2, where the bound is unchanged
--   - encoding: arbitrary randomized adaptive algorithms with sample access to d coins, using N samples, output in ℝ^d ∪ {⊥} → the published SamplingAlgorithm d N (arbitrary probability seed space, prefix-dependent coin choices, fixed horizon N) with failure as none; reason: the base mission's model of §3.2 and Appendix B; private randomness is in the seed and an algorithm that stops early is padded with ignored tosses, so N is the worst-case toss count
--   - reading: N = O((d²/ε²) log(d/δ) log(1/δ)) with ε, δ fixed first → one constant chosen before every other parameter; reason: the hidden constant cannot depend on ε, which appears inside the bound; the uniform reading is the stronger one
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Theorem 6.8, PDF p. 9 (= Theorem 4.3, PDF p. 3); proof Appendix A, PDF pp. 13–14

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Theorem 6.8 (= Theorem 4.3), PDF pp. 9, 3, corrected: the bound uses
δ' = min δ (1/2) (the printed bound with δ' = δ is false as δ → 1). The constant C
is chosen before d, ε, δ; N is the fixed (worst-case) toss budget. Every d ∈ ℕ is
allowed: at d = 0 the bound is 0 and the zero-toss algorithm is list replicable. -/
theorem theorem_6_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ ε δ : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      δ ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ (N : ℕ) (A : SamplingAlgorithm d N), IsListReplicable A (d + 1) ε δ ∧
        (N : ℝ) ≤ C * (d : ℝ) ^ 2 / ε ^ 2 * Real.log ((d : ℝ) / min δ (1 / 2)) *
          Real.log (1 / min δ (1 / 2)) := by sorry

end ListReplicableBias.LowerBound.Supplement
