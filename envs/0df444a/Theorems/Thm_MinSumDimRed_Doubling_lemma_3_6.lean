-- Prove2me | Theorems.Thm_MinSumDimRed_Doubling_lemma_3_6
-- name    : MinSumDimRed.Doubling.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:35:48.738174+00:00
-- url     : https://prove2.me/theorems/21f4a2cb-ec7c-4bc8-b00c-d88b91e7dffd
-- title:
--   Lemma 3.6 — preservation of a random cluster: factor $(1+5\theta)(1+30\varepsilon)$, additive $O(\varepsilon(k\theta+n^{-8})\mathrm{OPT})$, probability $\ge 4/5$
-- statement:
--   **Lemma 3.6** (Preservation of a Random Cluster, p. 13). There are absolute constants $\alpha, \beta > 0$ and $K > 0$ (the constant of the $O(\cdot)$) such that the following holds. Let $X = \{p_0, \dots, p_{n-1}\} \subseteq \mathbb R^d$ be an instance of min-sum $k$-clustering ($n$ distinct points) of doubling dimension at most $\mathrm{ddim} \ge 1$, and let $\mathrm{OPT}$ be its optimal min-sum $k$-clustering cost. Assume $0 < \varepsilon \le 1/10$ and
--   $$\theta \le \tfrac{1}{20}, \qquad \delta \le \min\Big\{\frac{\theta^7}{600},\ \frac{\varepsilon^{\alpha\,\mathrm{ddim}}}{100 k^2 \log^2 n}\Big\}, \qquad \mu \ge \beta\big(\mathrm{ddim}\log(1/\varepsilon) + \log k + \log\log n\big).$$
--   Let $f : \mathbb R^d \to \mathbb R^t$ be a random map on a probability space such that $\Pr[\|f(x) - f(y)\| \notin (1 \pm \varepsilon)\|x - y\|] \le \delta$ for all $x, y \in X$, and assume $f$ has the $\mu$-local ball-tail property for $X$. Then for every random subset $C \subseteq X$ (which may depend on $f$), with probability at least $4/5$, both
--   $$\mathrm{cost}(C) \le A\big(\mathrm{cost}(f(C)) + K\varepsilon(k\theta + n^{-8})\mathrm{OPT}\big) \quad (5)$$
--   $$\mathrm{cost}(f(C)) \le A\big(\mathrm{cost}(C) + K\varepsilon(k\theta + n^{-8})\mathrm{OPT}\big) \quad (6)$$
--   hold, where $A = (1 + 5\theta)(1 + 30\varepsilon)$ and costs are over ordered pairs. Here $\log^2 n = (\log n)^2$.
--
--   Differences from the source:
--   - reading: sufficiently large constants α, β > 0 and the constant of O(ε(kθ + n^{−8})OPT) → explicit existential constants (∃ … > 0) quantified before every instance parameter; reason: one universal constant; since every hypothesis containing it gets stronger as it grows, 'sufficiently large' is equivalent to 'some'
--   - encoding: O(ε(kθ + n^{−8})OPT) → K · ε · (k·θ + ((n : ℝ)^8)⁻¹) · OPT with K > 0 from the leading ∃; reason: an O(·) with an absolute constant, uniform over all instances
--   - encoding: a finite point set X ⊆ ℝ^d with n = |X| points → an injective family p : Fin n → EuclideanSpace ℝ (Fin d), X = Set.range p; reason: same instances: injectivity makes the n indexed points distinct, so |X| = n
--   - encoding: doubling dimension at most ddim ≥ 1 → 1 ≤ D ∧ HasDoublingDimAtMost (Set.range p) D; reason: equivalent to ddim(X) ≤ D (the infimum is attained) and never satisfied by a non-doubling set
--   - encoding: OPT, the optimal min-sum k-clustering cost of X (cost of an optimal k-partition P*) → MinSumFPT.optCost (eucl p) k = infimum of labCost over labellings σ : Fin n → Fin k; reason: for 1 ≤ k ≤ n it equals the minimum over partitions into exactly k nonempty parts (splitting a part never increases the cost); for k > n, where no such partition exists, it is 0, and for k = 0 (not an instance) it is 0; P* itself appears only in the proof
--   - encoding: random map f : ℝ^d → ℝ^t; random subset C ⊆ X which may depend on f → f : Ω → Pt d → Pt t with each ω ↦ f ω x measurable (IsRandomMap); C : Ω → Finset (Fin n) with measurable membership events (IsRandomSubset), on one probability space (Ω, μ) of arbitrary type; no independence between C and f; reason: a random object is a random variable on the probability space carrying f
--   - reading: a ∈ (1 ± ε) b → WithinFactor ε a b, i.e. (1 − ε)·b ≤ a ∧ a ≤ (1 + ε)·b (closed interval); reason: the paper does not say open or closed; the closed interval is the standard meaning and both inequalities are kept
--   - reading: log (base unspecified) → Real.log (natural logarithm); reason: any fixed base only rescales the absolute constants, which are existentially quantified
--   - encoding: ε^{α ddim}/(100k² log² n) and log log n where they are undefined (k = 0 or n ≤ 1) → Lean's conventions x/0 = 0 and Real.log 0 = 0; reason: only cases outside the source's scope or trivial: for n ≤ 1 every cost is 0 and both conclusions hold for every outcome; k = 0 is not an instance (δ ≤ 0 is then forced, and no hypothesis of the source is dropped)
--   - encoding: with probability at least p / Pr[event] ≤ q → p ≤ μ.real {ω | …} / μ.real {ω | …} ≤ q on a probability measure μ; reason: μ.real is the (outer) measure as a real number; no measurability of the event is presupposed, and for measurable events it is the probability
-- source:
--   Asaf Dallal, Robert Krauthgamer, Dimension Reduction and Coresets for Min-Sum k-Clustering, arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), p. 13 (PDF 13), Lemma 3.6 (proof pp. 13–15)

import Mathlib
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumDimRed_Doubling_Metric
import Definitions.Def_MinSumDimRed_Doubling_Costs
import Definitions.Def_MinSumDimRed_Doubling_Random

open MeasureTheory ProbabilityTheory

namespace MinSumDimRed.Doubling

/-- Lemma 3.6 (Preservation of a Random Cluster), p. 13. There are absolute constants `α, β > 0`
(the "sufficiently large constants") and `K > 0` (the constant of the `O(·)`) such that the
following holds. Let `X = {p 0, …, p (n-1)} ⊆ ℝ^d` (`n` distinct points) have doubling dimension
at most `ddim ≥ 1`, let `k ∈ ℕ` and `OPT` be the optimal min-sum `k`-clustering cost of `X`. Assume
`0 < ε ≤ 1/10`, `θ ≤ 1/20`, `δ ≤ min{θ^7/600, ε^{α ddim}/(100 k² log² n)}` and
`µ ≥ β (ddim log(1/ε) + log k + log log n)`. Let `f : ℝ^d → ℝ^t` be a random map on a probability
space with `Pr[‖f(x) - f(y)‖ ∉ (1 ± ε)‖x - y‖] ≤ δ` for all `x, y ∈ X`, having the `µ`-local
ball-tail property for `X`. Then for every random subset `C ⊆ X` (which may depend on `f`), with
probability at least `4/5`, both
(5) `cost(C) ≤ A (cost(f(C)) + K ε (kθ + n^{-8}) OPT)` and
(6) `cost(f(C)) ≤ A (cost(C) + K ε (kθ + n^{-8}) OPT)` hold, where `A = (1 + 5θ)(1 + 30ε)`. -/
theorem lemma_3_6 :
    ∃ α β K : ℝ, 0 < α ∧ 0 < β ∧ 0 < K ∧
      ∀ (d t n k : ℕ) (p : Fin n → Pt d), Function.Injective p →
      ∀ D : ℝ, 1 ≤ D → HasDoublingDimAtMost (Set.range p) D →
      ∀ ε θ δ mu : ℝ, 0 < ε → ε ≤ 1 / 10 → θ ≤ 1 / 20 →
        δ ≤ min (θ ^ 7 / 600)
              (ε ^ (α * D) / (100 * (k : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 2)) →
        β * (D * Real.log (1 / ε) + Real.log (k : ℝ) + Real.log (Real.log (n : ℝ))) ≤ mu →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (f : Ω → Pt d → Pt t), IsRandomMap f →
        (∀ i j : Fin n,
          μ.real {ω | ¬ WithinFactor ε ‖f ω (p i) - f ω (p j)‖ ‖p i - p j‖} ≤ δ) →
        HasLocalBallTail μ f (Set.range p) mu →
      ∀ C : Ω → Finset (Fin n), IsRandomSubset C →
        (4 / 5 : ℝ) ≤ μ.real {ω |
          setCost p (C ω) ≤
              (1 + 5 * θ) * (1 + 30 * ε) *
                (imgSetCost (f ω) p (C ω) +
                  K * ε * ((k : ℝ) * θ + ((n : ℝ) ^ 8)⁻¹) * MinSumFPT.optCost (eucl p) k) ∧
          imgSetCost (f ω) p (C ω) ≤
              (1 + 5 * θ) * (1 + 30 * ε) *
                (setCost p (C ω) +
                  K * ε * ((k : ℝ) * θ + ((n : ℝ) ^ 8)⁻¹) * MinSumFPT.optCost (eucl p) k)} := by sorry

end MinSumDimRed.Doubling
