-- Prove2me | Theorems.Thm_ObliviousAdaptive172_Parallel_fixed_output_adaptive_transfer
-- name    : ObliviousAdaptive172.Parallel.fixed_output_adaptive_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:48.490207+00:00
-- url     : https://prove2.me/theorems/0af53712-9b8a-4947-b241-813c006f178a
-- title:
--   Claim 3.1 — fixed-output adaptive transfer
-- statement:
--   Let $P\Rightarrow P'\Rightarrow P''$ be three monotone properties on legal histories, with $P''$ equivalent to the existence of a valid configuration. Let ALG be a causal private-tape dynamic algorithm whose published answers consist of “no” followed by a single fixed configuration. Fix graph-size parameter $n\ge2$, confidence exponent $c>0$, finite horizon $m$ and actual work budget $T$.
--
--   Suppose that for every legal, obliviously fixed history of length at most $m$, one joint event of probability at least $1-n^{-c}$ has all three properties: total work at most $T$; “no” at every step strictly before $P'$ holds; and a valid $P''$-configuration actually computed and stored by the first $P'$ step. Then for every legal output-observing adaptive policy, including policies with independent private randomness, one joint event of probability at least $1-n^{-c}$ satisfies
--
--   $$
--   \operatorname{work}\bigl(\text{through the first }P'\text{ step}\bigr)\le T,
--   \qquad\text{“no” before }P',
--   \qquad\text{a valid }P''\text{ configuration stored by that step}.
--   $$
--
--   If $P'$ never holds, the work and “no” requirements cover the entire run and the storage requirement has no deadline. If it holds initially, the deadline is action zero. This transfers the fixed-output prefix guarantee without asserting a runtime bound on the whole post-deadline adaptive continuation. All three properties and both implications are retained.
--
--   **Formalization Note** Legal histories, execution and actual storage use the shared definitions. The private algorithm tape and adversary tape have product law. Induced property, output, work-threshold and stored-validity events are explicitly required to be measurable, without imposing any probability bound. There is no independence assumption after conditioning on “no”.
--
--   Differences from the source:
--   - generalization: graph states and legal incremental or decremental updates → arbitrary legal history transition systems, with graph histories as instances; reason: no graph instance is excluded, and the history-dependent synthetic property in §3.3 is expressible
--   - encoding: a randomized dynamic algorithm with internal storage and update time → a causal private-tape instruction machine, actual witness-handle memory and executed instruction costs, with divergence assigned infinite cost; reason: this exposes computation and storage rather than accepting either as an arbitrary supplied certificate
--   - encoding: probabilities over independent private randomness and an output-observing adaptive adversary → arbitrary probability measures, their actual product law, measurable witnessing success events and explicit measurability of induced execution events; reason: the source probability assertions presuppose measurable events; this adds no probability, correctness or runtime bound and imposes no finite-support condition
--   - encoding: a finite stream and its first property-holding step → arbitrary finite horizons, policies allowed to stop, initialization as action zero and an optional first hit; reason: the empty or initially satisfying stream is retained; when there is no hit, prefix runtime covers the entire delivered stream without a false storage deadline
-- source:
--   Shiri Chechik, Inbal Hadad, From Oblivious to Adaptive Adversaries: Black-Box Reductions for Monotone Dynamic Problems with Applications to Cuts, Distances, and Clustering, STOC 2027 submission #172 (October 2026), p. 9, Claim 3.1 (PDF p. 11); proof pp. 27–28, Appendix A.1 (PDF pp. 29–30)

import Mathlib
import Definitions.Def_ObliviousAdaptive172_Parallel_PrivateTapeExecution
set_option autoImplicit false

namespace ObliviousAdaptive172.Parallel

open MeasureTheory

/-- Claim 3.1, printed p.9 (PDF p.11). History-state generalization permits the
synthetic intermediate property of §3.3; costs/storage are actual machine executions.
The optional deadline includes initialization and covers the whole run if never hit. -/
theorem fixed_output_adaptive_transfer
    {U W R Q : Type}
    [MeasurableSpace R] (μ : Measure R) [IsProbabilityMeasure μ]
    (M : HistoryModel U) (A : PrivateTapeExecution U W R Q)
    (P P' P'' : List U → Prop) (valid : List U → W → Prop)
    (n : ℕ) (c : ℝ) (T m : ℕ) (hn : 2 ≤ n) (hc : 0 < c)
    (hmono : M.Monotone P ∧ M.Monotone P' ∧ M.Monotone P'')
    (himp : ∀ h, M.Legal h → (P h → P' h) ∧ (P' h → P'' h))
    (hwitness : ∀ h, M.Legal h → (P'' h ↔ ∃ w, valid h w))
    (hfixed : FixedOutput M A)
    (hoblivious : ∀ h, M.Legal h → h.length ≤ m →
      WithProbability μ (1 - (n : ℝ) ^ (-c)) (fun r =>
        (machineRun A r h).work ≤ T ∧ NoEarly A r P' h ∧ StoredAtHit A r P' valid h)) :
    ∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
      (π : OutputPolicy U W Ξ), AdmissiblePolicy M π →
      let H := fun z : R × Ξ =>
        (interact (fun h => (machineRun A z.1 h).observation) π z.2 m).history
      ExecutionEventsMeasurable H
        (fun z h => (machineRun A z.1 h).answer)
        (fun z h => (machineRun A z.1 h).work) P'
        (fun z h => ∃ w, (machineRun A z.1 h).Stored w ∧ valid h w) →
      WithProbability (μ.prod ν) (1 - (n : ℝ) ^ (-c)) (fun z =>
        let h := H z
        (machineRun A z.1 (h.take ((firstHit P' h).getD h.length))).work ≤ T ∧
        NoEarly A z.1 P' h ∧ StoredAtHit A z.1 P' valid h) := by sorry

end ObliviousAdaptive172.Parallel
