-- Prove2me | Theorems.Thm_MinSumDimRed_Doubling_theorem_1_2
-- name    : MinSumDimRed.Doubling.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:35:54.123126+00:00
-- url     : https://prove2.me/theorems/bd1fd8d5-29e9-47aa-9d54-f560d41b78a8
-- title:
--   Theorem 1.2 — Gaussian JL to $t \ge c\varepsilon^{-2}(\mathrm{ddim}(X)\log\frac1\varepsilon + \log k + \log\log n)$ dimensions preserves every $k$-partition's min-sum cost within $1\pm\varepsilon$
-- statement:
--   **Theorem 1.2** (Euclidean Dimension Reduction for Doubling Sets, p. 4). There is an absolute constant $c > 0$ such that the following holds. Let $X \subseteq \mathbb R^d$ be a finite set of $n$ points, $k \in \mathbb N$ and $0 < \varepsilon < 1/4$, and let $f : \mathbb R^d \to \mathbb R^t$ be a Gaussian JL map ($f(x) = Wx$, $W$ a $t \times d$ matrix with independent $N(0, 1/t)$ entries) with
--   $$t \ge c\,\varepsilon^{-2}\big(\mathrm{ddim}(X)\log(1/\varepsilon) + \log k + \log\log n\big).$$
--   Then, with probability at least $4/5$, for every $k$-partition $P = \{P_1, \dots, P_k\}$ of $X$ simultaneously,
--   $$\mathrm{cost}(f(P)) \in (1 \pm \varepsilon)\,\mathrm{cost}(P),$$
--   where $\mathrm{cost}(P) = \sum_{i=1}^k \sum_{x, y \in P_i} \|x - y\|$ is the min-sum objective (1) over ordered pairs and $\mathrm{cost}(f(P)) = \sum_i \sum_{x, y \in P_i} \|f(x) - f(y)\|$ (images as multisets). $\mathrm{ddim}(X)$ is the doubling dimension of $X$ with its own balls, floor $1$.
--
--   **Formalization Note** The event is a single event containing the for-all over partitions, as printed: one draw of $W$ must work for all partitions at once.
--
--   Differences from the source:
--   - reading: a sufficiently large constant c > 0 → explicit existential constants (∃ … > 0) quantified before every instance parameter; reason: one universal constant; since every hypothesis containing it gets stronger as it grows, 'sufficiently large' is equivalent to 'some'
--   - encoding: a finite point set X ⊆ ℝ^d with n = |X| points → an injective family p : Fin n → EuclideanSpace ℝ (Fin d), X = Set.range p; reason: same instances: injectivity makes the n indexed points distinct, so |X| = n
--   - generalization: every k-partition P = {P_1, …, P_k} of X → every labelling σ : Fin n → Fin k (part i = σ⁻¹(i)); parts may be empty; reason: every partition of X into k nonempty parts is such a labelling, so the for-all conclusion over more partitions specializes to the source; the paper itself allows partitions into at most k parts in §4
--   - encoding: cost(f(P)) over the multisets f(P_i) → MinSumFPT.labCost (imgDist f p) σ = Σ_i Σ_{x,y: σx=σy=i} ‖f(p x) − f(p y)‖; reason: sums over the points of X, so coinciding images are counted with multiplicity exactly as the p. 3 multisets
--   - encoding: Gaussian JL map f : ℝ^d → ℝ^t, a matrix with independent N(0, 1/t) entries → W drawn from gaussianJLLaw t d = UnderstandingML.gaussianMatrixLaw t d (t : NNReal)⁻¹ (entries gaussianReal 0 (1/t), second argument the variance), f = jlMap W, x ↦ W x; reason: the published product Gaussian law; 1/t is the variance as in N(0, 1/t)
--   - reading: a ∈ (1 ± ε) b → WithinFactor ε a b, i.e. (1 − ε)·b ≤ a ∧ a ≤ (1 + ε)·b (closed interval); reason: the paper does not say open or closed; the closed interval is the standard meaning and both inequalities are kept
--   - reading: log (base unspecified) → Real.log (natural logarithm); reason: any fixed base only rescales the absolute constants, which are existentially quantified
--   - encoding: target dimension t → t : ℕ, with the hypothesis on (t : ℝ); reason: dimensions are natural numbers
--   - encoding: ddim(X) → ddim (Set.range p) = sInf {D | IsDoublingWith (Set.range p) D}; reason: a finite set is always doubling, the admissible exponents form a closed up-ray [D₀, ∞) with D₀ ≥ 1, so the infimum is the paper's minimum
--   - encoding: log k, log log n where undefined (k = 0, n ≤ 1) → Real.log junk values (Real.log 0 = 0); reason: only cases outside the source's scope or trivial: for n ≤ 1 every cost is 0 and the event holds for every W; for k = 0 and n ≥ 1 there is no labelling and the event is everything
--   - encoding: with probability at least p / Pr[event] ≤ q → p ≤ μ.real {ω | …} / μ.real {ω | …} ≤ q on a probability measure μ; reason: μ.real is the (outer) measure as a real number; no measurability of the event is presupposed, and for measurable events it is the probability
-- source:
--   Asaf Dallal, Robert Krauthgamer, Dimension Reduction and Coresets for Min-Sum k-Clustering, arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), p. 4 (PDF 4), Theorem 1.2 (restated p. 10, proved p. 16)

import Mathlib
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumDimRed_Doubling_Metric
import Definitions.Def_MinSumDimRed_Doubling_Costs
import Definitions.Def_MinSumDimRed_Doubling_Random

open MeasureTheory ProbabilityTheory

namespace MinSumDimRed.Doubling

/-- Theorem 1.2 (Euclidean Dimension Reduction for Doubling Sets), p. 4. There is an absolute
constant `c > 0` such that for every finite `X = {p 0, …, p (n-1)} ⊆ ℝ^d` (`n` distinct points),
every `k` and every `0 < ε < 1/4`, if `t ≥ c ε^{-2} (ddim(X) log(1/ε) + log k + log log n)`, then a
Gaussian JL map `f(x) = W x` (`W` a `t × d` matrix with i.i.d. `N(0, 1/t)` entries) satisfies,
with probability at least `4/5`, simultaneously for every `k`-partition `P` of `X` (a labelling
`σ : Fin n → Fin k`), `cost(f(P)) ∈ (1 ± ε) cost(P)`, where `cost` is the min-sum objective (1)
over ordered pairs. -/
theorem theorem_1_2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d n k : ℕ) (p : Fin n → Pt d), Function.Injective p →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ∀ t : ℕ,
        c * (ε ^ 2)⁻¹ *
            (ddim (Set.range p) * Real.log (1 / ε) + Real.log (k : ℝ) +
              Real.log (Real.log (n : ℝ))) ≤ (t : ℝ) →
        (4 / 5 : ℝ) ≤ (gaussianJLLaw t d).real {W | ∀ σ : Fin n → Fin k,
          WithinFactor ε (MinSumFPT.labCost (imgDist (jlMap W) p) σ)
            (MinSumFPT.labCost (eucl p) σ)} := by sorry

end MinSumDimRed.Doubling
