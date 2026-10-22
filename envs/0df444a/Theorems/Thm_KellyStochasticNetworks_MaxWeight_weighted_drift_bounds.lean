-- Prove2me | Theorems.Thm_KellyStochasticNetworks_MaxWeight_weighted_drift_bounds
-- name    : KellyStochasticNetworks.MaxWeight.weighted_drift_bounds
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:47.481632+00:00
-- url     : https://prove2.me/theorems/01e07153-c8ac-4251-aff2-5cd8270417fc
-- title:
--   Exercise 7.18 — uniform weighted drift bounds
-- statement:
--   Let $R$ be a finite nonempty queue set, $S$ a finite nonempty downward-closed schedule family, $\alpha>0$, and $\lambda\in\operatorname{int}\Lambda$. Run MaxWeight-$\alpha$ with independent Poisson arrivals of rates $\lambda_r$ and a fixed random tie rule supported on maximizing schedules. Write $q'$ for the next queue state and $D(q)=\sum_rq_r^\alpha\mathbb E[q'_r-q_r\mid q]$.
--
--   Every coordinate increment is integrable. There exist constants $\epsilon>0$, $K>0$, and $b\in\mathbb R$ such that
--   $$\|q\|_2>K\ \Longrightarrow\ D(q)<-\epsilon\|q\|_2^\alpha,\qquad \|q\|_2\le K\ \Longrightarrow\ D(q)<b.$$
--   The same constants work for every queue vector and every time. These are the main-drift estimates required in the stability argument.
--
--   **Formalization Note** The inequalities are pointwise bounds on the conditional drift in (7.14); the exercise's conditioning on the large/small region denotes the respective regimes. Constants may depend on the fixed network, exponent, rates, and tie rule, but not on queue size or time. Actual departures are $\min(q_r,\sigma_r)$, including at zero queues. The book leaves the norm unspecified; the Euclidean norm is chosen explicitly.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 182 (PDF p. 190), Exercise 7.18; DOI 10.1017/cbo9781139565363

import Definitions.Def_KellyStochasticNetworks_MaxWeight_Network

open scoped NNReal

/- Imported dependency source, reproduced verbatim for standalone inspection.
/-- A discrete-time transition law on a countable state space. -/
def Chain (S : Type*) := S → PMF S

/-- Probability of reaching `j` in exactly `n` transitions from `i`. -/
noncomputable def transitionPower {S : Type*} (P : Chain S) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | n + 1, i, j => ∑' k, P i k * transitionPower P n k j

/-- Every state communicates with every other state. -/
def Irreducible {S : Type*} (P : Chain S) : Prop :=
  ∀ i j, ∃ n : ℕ, 0 < transitionPower P n i j

/-- Probability that times 1 through n all avoid K, starting from i at time 0. -/
noncomputable def avoidProbability {S : Type*} (P : Chain S) (K : Set S) :
    ℕ → S → ℝ≥0∞
  | 0, _ => 1
  | n + 1, i => ∑' j, if j ∈ K then 0 else P i j * avoidProbability P K n j

/-- Extended expected strictly positive hitting time, using the tail-sum formula.
Non-return has infinite cost, even if it occurs with positive probability less than one. -/
noncomputable def meanReturn {S : Type*} (P : Chain S) (K : Set S) (i : S) : ℝ≥0∞ :=
  ∑' n : ℕ, avoidProbability P K n i

/-- Every state has finite expected strictly positive return time. -/
def PositiveRecurrent {S : Type*} (P : Chain S) : Prop :=
  ∀ i, meanReturn P {i} i < ∞

/-- Real one-step drift; use only with the separately asserted absolute summability. -/
noncomputable def drift {S : Type*} (P : Chain S) (L : S → ℝ) (i : S) : ℝ :=
  ∑' j, (P i j).toReal * (L j - L i)

/-- Absolute integrability of a one-step increment on the countable state space. -/
def DriftIntegrable {S : Type*} (P : Chain S) (L : S → ℝ) (i : S) : Prop :=
  Summable (fun j => (P i j).toReal * |L j - L i|)

/-- The finite, nonempty, downward-closed family of integer service schedules. -/
structure Network (R : Type*) [Fintype R] where
  schedules : Finset (R → ℕ)
  nonempty : schedules.Nonempty
  downward : ∀ σ ∈ schedules, ∀ π : R → ℕ, (∀ r, π r ≤ σ r) → π ∈ schedules

/-- Nonnegative arrival vectors dominated by a convex combination of schedules. -/
def capacityRegion {R : Type*} [Fintype R] (N : Network R) : Set (R → ℝ) :=
  {v | (∀ r, 0 ≤ v r) ∧ ∃ c : (R → ℕ) → ℝ,
    (∀ σ ∈ N.schedules, 0 ≤ c σ) ∧
    (∑ σ ∈ N.schedules, c σ) = 1 ∧
    ∀ r, v r ≤ ∑ σ ∈ N.schedules, c σ * (σ r : ℝ)}

noncomputable def scheduleWeight {R : Type*} [Fintype R]
    (α : ℝ) (q σ : R → ℕ) : ℝ :=
  ∑ r, (σ r : ℝ) * (q r : ℝ) ^ α

/-- A fixed state-dependent random tie rule, supported on maximizing schedules.
No distribution among ties is specified by the source. -/
def IsMaxWeight {R : Type*} [Fintype R] (N : Network R) (α : ℝ)
    (tie : (R → ℕ) → PMF (R → ℕ)) : Prop :=
  ∀ q σ, tie q σ ≠ 0 → σ ∈ N.schedules ∧
    ∀ π ∈ N.schedules, scheduleWeight α q π ≤ scheduleWeight α q σ

/-- Independent arrivals in a unit slot, with the stated Poisson rates. -/
noncomputable def arrivalLaw {R : Type*} [Fintype R] (lam : R → ℝ≥0) : PMF (R → ℕ) :=
  (Measure.pi (fun r => poissonMeasure (lam r))).toPMF

/-- Departures precede the new slot's arrivals. Natural subtraction suppresses unused service. -/
def nextQueue {R : Type*} (q σ a : R → ℕ) : R → ℕ :=
  fun r => q r - σ r + a r

/-- Actual homogeneous queue transition law: random schedule independent of fresh arrivals. -/
noncomputable def queueChain {R : Type*} [Fintype R] (lam : R → ℝ≥0)
    (tie : (R → ℕ) → PMF (R → ℕ)) : Chain (R → ℕ) :=
  fun q => (tie q).bind (fun σ => (arrivalLaw lam).map (nextQueue q σ))

/-- Euclidean queue size, made explicit rather than using the function-space sup norm. -/
noncomputable def queueNorm {R : Type*} [Fintype R] (q : R → ℕ) : ℝ :=
  Real.sqrt (∑ r, (q r : ℝ) ^ (2 : ℕ))

/-- The main drift in (7.14), using actual capped departures through the queue kernel. -/
noncomputable def weightedDrift {R : Type*} [Fintype R] (α : ℝ)
    (P : Chain (R → ℕ)) (q : R → ℕ) : ℝ :=
  ∑ r, (q r : ℝ) ^ α * drift P (fun x => (x r : ℝ)) q

/-- Coordinatewise finite service envelope used in Exercise D.1. -/
noncomputable def serviceBound {R : Type*} [Fintype R] (N : Network R) (r : R) : ℕ :=
  N.schedules.sup (fun σ => σ r)

/-- The envelope Y is the maximum of one Poisson arrival count and the service bound. -/
def incrementEnvelope (B a : ℕ) : ℝ := (max a B : ℕ)

/-- The second term of Exercise D.1(2), written as a tail integral.
This avoids a conditional expectation on a zero-probability tail event. -/
noncomputable def poissonTailRemainder (lam : ℝ≥0) (B : ℕ) (α δ K : ℝ) : ℝ :=
  ∫ a : ℕ, if δ * K < incrementEnvelope B a then
      |(1 + incrementEnvelope B a / K) ^ (α + 1)| + 1 else 0
    ∂poissonMeasure lam
-/

namespace KellyStochasticNetworks.MaxWeight

theorem weighted_drift_bounds {R : Type*} [Fintype R] [Nonempty R]
    (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N))
    (tie : (R → ℕ) → PMF (R → ℕ)) (htie : IsMaxWeight N α tie) :
    (∀ q r, DriftIntegrable (queueChain lam tie) (fun x => (x r : ℝ)) q) ∧
    ∃ ε K b : ℝ, 0 < ε ∧ 0 < K ∧
      (∀ q, K < queueNorm q →
        weightedDrift α (queueChain lam tie) q < -ε * queueNorm q ^ α) ∧
      (∀ q, queueNorm q ≤ K → weightedDrift α (queueChain lam tie) q < b) := by sorry

end KellyStochasticNetworks.MaxWeight
