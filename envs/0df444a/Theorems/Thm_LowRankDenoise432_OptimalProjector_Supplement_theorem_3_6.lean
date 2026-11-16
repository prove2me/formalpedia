-- Prove2me | Theorems.Thm_LowRankDenoise432_OptimalProjector_Supplement_theorem_3_6
-- name    : LowRankDenoise432.OptimalProjector.Supplement.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:41:40.253205+00:00
-- url     : https://prove2.me/theorems/aad9fa01-d068-401d-9d9d-271337a6a7e7
-- title:
--   Theorem 3.6 — suboptimality probability of the projection estimator (all four clauses)
-- statement:
--   Work in the model of Section 2: a random cost $c\in\mathbb R^d$ with mean $\bar c$, and $m\ge1$ replications $\varepsilon^{(1)},\dots,\varepsilon^{(m)}$ with $|\varepsilon^{(r)}_e|\le b$, mean zero given $c$, and, given $c$, independent with independent coordinates (the scalar noises $\varepsilon^{(r)}_e$ are conditionally jointly independent given $c$). Let $\mathcal Z\subseteq\{0,1\}^d$ be a nonempty finite family of paths, each with at most $L$ edges, and let $\hat z$ be any measurable choice, at each outcome, of a minimizer of $\hat c_\Pi^\top z$ over $\mathcal Z$ (ties broken in any measurable way). Let $\Pi$ be a fixed orthogonal projector of rank $k$, put $\rho=\max_e\Pi_{ee}$ and
--   $$\hat c_\Pi=\bar c+\Pi(\bar y_m-\bar c),\qquad \text{regret}=c^\top\hat z-\min_{z\in\mathcal Z}c^\top z,$$
--   and let $\Delta=\Delta(c)$ be the path gap. Probabilities are conditional on $c$; each bound holds for almost every outcome whose cost $c$ satisfies the stated hypothesis.
--
--   1. If $(I-\Pi)(c-\bar c)=0$, then for every $t>0$
--   $$\mathbb P\big(\|\hat c_\Pi-c\|_\infty\ge t\mid c\big)\le 2d\exp\Big(-\frac{mt^2}{2b^2\rho}\Big).$$
--   2. If $(I-\Pi)(c-\bar c)=0$, then
--   $$\mathbb P(\text{regret}>0\mid c)\le 2d\exp\Big(-\frac{m\Delta^2}{8L^2b^2\rho}\Big).$$
--   3. If moreover $\rho\le\mu k/d$ for some $\mu>0$, both exponents exceed those of the sample mean ($\rho=1$) by the factor $d/(\mu k)$: the two bounds hold with $2d\exp(-mt^2d/(2b^2\mu k))$ and $2d\exp(-m\Delta^2d/(8L^2b^2\mu k))$.
--   4. If instead $\beta=\|(I-\Pi)(c-\bar c)\|_2\le\Delta/(4L)$ (with no zero-bias assumption), then
--   $$\mathbb P(\text{regret}>0\mid c)\le 2d\exp\Big(-\frac{m\Delta^2}{32L^2b^2\rho}\Big).$$
--
--   If every path is optimal for $c$, the regret bounds read $\mathbb P(\text{regret}>0\mid c)\le 0$. A bound $2d\exp(-a/s)$ with $s=0$ (no noise, $\rho=0$, or $k=0$) is read as $0$.
--
--   The theorem shows that the chance of choosing a suboptimal path decays exponentially in $m\Delta^2$, at a rate improved by the projection whenever its diagonal is small, and that a small bias only changes the constant in the exponent.
--
--   **Formalization Note.** $\mathbb P(A\mid c)$ is the conditional expectation of $\mathbf 1_A$ given $\sigma(c)$; the hypotheses on $c$ are imposed pointwise on the outcome, so no uniform margin or bias condition over all costs is assumed. $\Pi$ is a deterministic matrix, the held-fixed reading of "independent of the test noise". `expTail d a s` is $2d\exp(-a/s)$, and $0$ when $s=0$. The conditions $\rho\le\mu k/d$ and $\beta\le\Delta/(4L)$ are written $d\rho\le\mu k$ and $4L\beta\le\Delta$.
--
--   Differences from the source:
--   - reading: Π a rank-k projector independent of the test noise → Π a fixed (deterministic) orthogonal projector, k = rank Π; reason: the displayed bounds use ρ as a constant and the proof conditions on Π; a projector chosen independently of the test noise is covered by conditioning on its selection
--   - encoding: given c, the replications are independent with independent coordinates → conditional joint independence of all ε⁽ʳ⁾ₑ given σ(c), by product factorization for bounded measurable test functions, added to the published model; reason: the published model records only conditional second moments, which do not suffice for Hoeffding; this is Section 2's assumption, not a new one
--   - generalization: 𝒵 the set of source-to-sink paths of a DAG with at most L edges each → any nonempty finite family of 0/1 vectors with at most L ones each; reason: the proof uses only these properties, and every path set of a DAG is such a family
--   - encoding: ẑ ∈ argmin ĉ_Πᵀz → any measurable random ẑ with ẑ(ω) ∈ argmin ĉ_Π(ω)ᵀz at every outcome; reason: the regret event must be measurable for its conditional probability; the bound is asserted for every such choice of minimizer, ties included
--   - encoding: P(· | c) under a hypothesis on c → the conditional expectation of the indicator given σ(c), bounded for almost every outcome whose c satisfies the hypothesis; reason: conditional probabilities given c are defined almost surely
--   - generalization: 2d exp(−a/s) undefined when s = 0 (b = 0, ρ = 0 or k = 0), and Δ undefined when every path is optimal → the bound is 0 in those cases; reason: in each such case the event has conditional probability 0; for s > 0 and some non-optimal path the printed bound is stated unchanged
--   - encoding: ρ ≤ μk/d and β ≤ Δ/(4L) → dρ ≤ μk and 4Lβ ≤ Δ (the latter assumed only when some path is not optimal); reason: equivalent for d, L ≥ 1; avoids division by zero
--   - reading: the exponent exceeds that of the sample mean (ρ = 1) by a factor d/(μk) → both bounds hold with ρ replaced by μk/d, i.e. exponents mt²d/(2b²μk) and mΔ²d/(8L²b²μk); reason: this is the quantitative content of the sentence (the sample-mean exponents are those with ρ = 1)
-- source:
--   Henry Aldridge-Krawciw, Irene Aldridge, Low-Rank Denoising for Predict-then-Optimize, STOC 2027 submission #432 (October 2026), source.pdf SHA-256 8d92579f841e1b4853ee9eecd477b739374858db635a23defcc3fb767b137889, PDF p.3, Theorem 3.6 (Suboptimality probability, Section 3.3); model PDF p.2 Section 2; proof PDF p.6

import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_LInftyNorm
import Definitions.Def_LowRankDenoise432_OptimalProjector_Model
import Definitions.Def_LowRankDenoise432_OptimalProjector_Supplement_Regret
open MeasureTheory ProbabilityTheory Matrix HighDimStat.SparseLinear

namespace LowRankDenoise432.OptimalProjector.Supplement

open Classical in
/-- Theorem 3.6 (Suboptimality probability), PDF p.3; proof PDF p.6. In the model of Section 2
(`M`, with `b = M.b` the noise bound) with the noise conditionally jointly independent given `c`,
let `𝒵` be a path family with at most `L` edges per path, `ẑ` any measurable choice of a
minimizer of `ĉ_Πᵀz` (ties broken arbitrarily), `Π = Q` a fixed orthogonal projector of rank `k = rank Q`, `ρ = maxₑ Πₑₑ`,
`ĉ_Π = c̄ + Π(ȳ_m − c̄)`, `Δ(c)` the path gap and `β = ‖(I − Π)(c − c̄)‖₂`. Conditional
probabilities are given `σ(c)`, and each bound holds for almost every outcome whose cost `c`
satisfies the stated hypothesis. `expTail d a s = 2d·exp(−a/s)` (read as `0` when `s = 0`).
1. if `(I − Π)(c − c̄) = 0`: `P(‖ĉ_Π − c‖∞ ≥ t | c) ≤ 2d exp(−mt²/(2b²ρ))` for every `t > 0`;
2. if `(I − Π)(c − c̄) = 0`: `P(regret > 0 | c) ≤ 2d exp(−mΔ²/(8L²b²ρ))`;
3. if `ρ ≤ μk/d` (`μ > 0`), the two exponents exceed the sample-mean ones (`ρ = 1`) by the factor
   `d/(μk)`: the bounds hold with `2d exp(−mt²d/(2b²μk))` and `2d exp(−mΔ²d/(8L²b²μk))`;
4. if instead `β ≤ Δ/(4L)` (no zero-bias assumption): `P(regret > 0 | c) ≤ 2d exp(−mΔ²/(32L²b²ρ))`.
When every path is optimal for `c` the regret probability is `0`. -/
theorem theorem_3_6 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m L : ℕ} (M : NoisyCostModel P d m) (hind : CondJointIndep M)
    (Z : Finset (Fin d → ℝ)) (hZ : IsPathFamily Z L)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsOrthProjector Q)
    (zhat : Ω → Fin d → ℝ) (hzhat : IsDecision M Z Q zhat) :
    -- (1) zero-bias error tail
    (∀ t : ℝ, 0 < t → ∀ᵐ ω ∂P, (1 - Q) *ᵥ (M.c ω - M.costMean) = 0 →
      condProbGivenCost M {ω' | t ≤ linfNorm (costEstimate M Q ω' - M.c ω')} ω ≤
        expTail d ((m : ℝ) * t ^ 2) (2 * M.b ^ 2 * maxDiag Q)) ∧
    -- (2) zero-bias suboptimality probability
    (∀ᵐ ω ∂P, (1 - Q) *ᵥ (M.c ω - M.costMean) = 0 →
      condProbGivenCost M (regretEvent M Z zhat) ω ≤
        if HasNonoptimal Z (M.c ω) then
          expTail d ((m : ℝ) * pathGap Z (M.c ω) ^ 2) (8 * (L : ℝ) ^ 2 * M.b ^ 2 * maxDiag Q)
        else 0) ∧
    -- (3) incoherence: exponents improved by the factor d/(μk)
    (∀ μ : ℝ, 0 < μ → (d : ℝ) * maxDiag Q ≤ μ * (Q.rank : ℝ) →
      (∀ t : ℝ, 0 < t → ∀ᵐ ω ∂P, (1 - Q) *ᵥ (M.c ω - M.costMean) = 0 →
        condProbGivenCost M {ω' | t ≤ linfNorm (costEstimate M Q ω' - M.c ω')} ω ≤
          expTail d ((m : ℝ) * t ^ 2 * d) (2 * M.b ^ 2 * μ * (Q.rank : ℝ))) ∧
      (∀ᵐ ω ∂P, (1 - Q) *ᵥ (M.c ω - M.costMean) = 0 →
        condProbGivenCost M (regretEvent M Z zhat) ω ≤
          if HasNonoptimal Z (M.c ω) then
            expTail d ((m : ℝ) * pathGap Z (M.c ω) ^ 2 * d)
              (8 * (L : ℝ) ^ 2 * M.b ^ 2 * μ * (Q.rank : ℝ))
          else 0)) ∧
    -- (4) small bias β ≤ Δ/(4L)
    (∀ᵐ ω ∂P,
      (HasNonoptimal Z (M.c ω) → 4 * (L : ℝ) * biasNorm M Q ω ≤ pathGap Z (M.c ω)) →
      condProbGivenCost M (regretEvent M Z zhat) ω ≤
        if HasNonoptimal Z (M.c ω) then
          expTail d ((m : ℝ) * pathGap Z (M.c ω) ^ 2) (32 * (L : ℝ) ^ 2 * M.b ^ 2 * maxDiag Q)
        else 0) := by sorry

end LowRankDenoise432.OptimalProjector.Supplement
