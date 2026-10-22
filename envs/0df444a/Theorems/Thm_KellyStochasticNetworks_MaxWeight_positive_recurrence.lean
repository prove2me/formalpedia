-- Prove2me | Theorems.Thm_KellyStochasticNetworks_MaxWeight_positive_recurrence
-- name    : KellyStochasticNetworks.MaxWeight.positive_recurrence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:55.97397+00:00
-- url     : https://prove2.me/theorems/84897908-ce1c-46c0-8cae-2b828532dab4
-- title:
--   Theorem 7.13 — positive recurrence under MaxWeight scheduling
-- statement:
--   Let $R$ be a finite nonempty set of queues and $S\subseteq\mathbb N^R$ a finite nonempty downward-closed family of service schedules. Packets arrive through independent Poisson processes with rates $\lambda_r$. Let $\Lambda$ be the admissible region of arrival vectors dominated by convex combinations of schedules. Fix any $\alpha>0$ and suppose $\lambda\in\operatorname{int}\Lambda$.
--
--   At each integer time, choose a schedule at random among the maximizers of $\sum_r\sigma_rq_r^\alpha$, using a fixed distribution depending only on the current queue vector. Serve $\min(q_r,\sigma_r)$ packets at queue $r$, and add the fresh independent arrivals. Then the resulting queue-length Markov chain is positive recurrent:
--   $$\forall q\in\mathbb N^R,\qquad \mathbb E_q[\tau_q^+]<\infty,\quad \tau_q^+=\inf\{n\ge1:q(n)=q\}.$$
--   This is the chapter's stability theorem for every positive MaxWeight exponent.
--
--   **Formalization Note** The capacity-region interior is the ordinary interior in $\mathbb R^R$, not relative interior in the nonnegative orthant. The homogeneous transition kernel is constructed from the schedule and Poisson laws. Expected return times are extended nonnegative tail sums, so a positive probability of never returning cannot be hidden by a default real value. No drift bound or recurrence assumption is imposed as a hypothesis.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 180 (PDF p. 188), Theorem 7.13, with standing model on pp. 177–179 and 213; DOI 10.1017/cbo9781139565363

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

theorem positive_recurrence {R : Type*} [Fintype R] [Nonempty R]
    (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N))
    (tie : (R → ℕ) → PMF (R → ℕ)) (htie : IsMaxWeight N α tie) :
    PositiveRecurrent (queueChain lam tie) := by sorry

end KellyStochasticNetworks.MaxWeight
