-- Prove2me | Theorems.Thm_OptStochMatch_Tight_lemma_2_4
-- name    : OptStochMatch.Tight.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:57:49.037794+00:00
-- url     : https://prove2.me/theorems/24fe4657-09f1-4d9a-9ca7-971324f0fa08
-- title:
--   Lemma 2.4 — online matching and online scheduling policies correspond, with equal laws and rewards
-- statement:
--   For Poisson arrivals with intensities $\lambda$ and the service-rate region $\mathcal P_\lambda$: every online matching policy has a scheduling counterpart and every online scheduling policy has a matching counterpart such that the processes of matched vertices and of completed jobs (identities with times) have the same law; and whenever a matching policy and a scheduling policy correspond in this sense, the expected matching size equals the expected total work processed.
--
--   Differences from the source:
--   - encoding: online policies: decisions from the current arrival, the history and independent internal randomization → PoissonPolicy / IIDPolicy: one Uniform[0,1] seed and a decision map measurable in the seed and arrival times; reason: a single uniform seed generates any independent internal randomness; past decisions are functions of the seed and past arrivals; same policy class
--   - encoding: nonanticipating scheduling policy (observed history and independent randomization) → SchedPolicy: a jointly measurable rate map of a Uniform[0,1] seed, the completion history and the time, in P, zero on completed jobs; reason: between completions the observed history is the elapsed time and the policy's own service; same policy class
--   - encoding: Poisson processes of intensities λ_S on [0,1] → Janossy densities e^{−∑λ_S} ∏ λ_{s_k} on ordered arrival times; reason: the law of the superposition of independent type-wise Poisson processes; same law
--   - encoding: the processes of matched vertices and completed jobs have the same law → for every j and measurable B ⊆ (ℝ × Fin m)^j, P(the record of (time, identity) pairs has exactly j entries and lies in B) agree; reason: a pure-jump process on [0,1] with at most m jumps is determined by its jump times and marks; same notion of equality in law
--   - reading: 'For corresponding policies, the expected matching size equals the expected total work' → for every pair of policies with the same record law; reason: the constructed counterparts are such pairs; the proof (via Lemma 2.1) uses only equality of laws
--   - encoding: ALG = E[total work] → ENNReal.ofReal ALG = expected total work in ℝ≥0∞; reason: ALG is finite and nonnegative; same equality
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Lemma 2.4, p. 8 (PDF p. 9)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Matching
import Definitions.Def_OptStochMatch_Tight_Scheduling
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace OptStochMatch.Tight

/-- Lemma 2.4 (p. 8, PDF 9). For Poisson arrivals with intensities `λ` and the service-rate
region `P_λ`: every online matching policy has a scheduling counterpart, and every online
scheduling policy has a matching counterpart, such that the processes of matched vertices and
of completed jobs (identities with their times) have the same law; and for corresponding
policies the expected matching size equals the expected total work processed. -/
theorem lemma_2_4 {m : ℕ} (lam : Ty m → ℝ≥0) :
    (∀ π : PoissonPolicy m, ∃ σ : SchedPolicy m (Plam lam), SameRecordLaw lam π σ) ∧
    (∀ σ : SchedPolicy m (Plam lam), ∃ π : PoissonPolicy m, SameRecordLaw lam π σ) ∧
    (∀ (π : PoissonPolicy m) (σ : SchedPolicy m (Plam lam)), SameRecordLaw lam π σ →
      ENNReal.ofReal (algPois lam π) = expTotalWork σ) := by sorry

end OptStochMatch.Tight
