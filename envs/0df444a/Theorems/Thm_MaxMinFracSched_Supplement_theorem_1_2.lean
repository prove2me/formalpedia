-- Prove2me | Theorems.Thm_MaxMinFracSched_Supplement_theorem_1_2
-- name    : MaxMinFracSched.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:24:44.413191+00:00
-- url     : https://prove2.me/theorems/430b5fae-bcbe-44db-87a8-ea35f9e7a109
-- title:
--   Theorem 1.2 — WeightedScaledEDF$(1/2)$ is $1/2$-competitive for the weighted objective and runs in worst-case $O(\log^3 n)$ time per arrival
-- statement:
--   In the weighted problem each job $j$ also carries a weight $\lambda_j>0$, revealed at its arrival. A schedule completing $c_j\le w_j$ work on $j$ by $d_j$ gives it value $\lambda_jc_j/w_j$, and $\hat f^{\lambda}_J$ is the largest minimum value an offline schedule can guarantee (not capped at $1$). WeightedScaledEDF$(\alpha')$ serves, at each time $t$, the earliest-deadline released, unexpired job whose work is below $\alpha'\hat f^{\lambda}_J(t)w_j/\lambda_j$, with $\hat f^{\lambda}_J(t)$ the weighted optimum of the jobs released by $t$, and idles if there is none.
--
--   **Theorem.**
--
--   1. *Competitive ratio.* Let $\prec$ be any strict total order on jobs that refines the deadline order. Then:
--      (a) some deterministic weighted online algorithm produces, on every valid instance with positive weights, a WeightedScaledEDF$(1/2)$ run for $\prec$;
--      (b) every WeightedScaledEDF$(1/2)$ run for $\prec$ on every valid instance $J$ with positive weights gives every job value
--   $$
--   \lambda_j f_j\ \ge\ \tfrac12\,\hat f^{\lambda}_J .
--   $$
--   2. *Implementation.* There are one deterministic real-RAM program and one constant $C>0$ such that for every $\alpha'>0$, every valid instance $J$ of $n$ jobs with positive weights and every presentation $L$ (each job given as $(d_j,w_j,\lambda_j)$), the event-driven run finishes without failure, its schedule is a WeightedScaledEDF$(\alpha')$ run for the order by deadline and then position in $L$, it has at most $C(n+1)$ operations, and every operation with $k$ arriving jobs takes at most $C(k+1)\log^3(n+2)$ instructions.
--
--   The first part extends the main result to weighted jobs; the second shows the weighted algorithm has the same worst-case update time as the unweighted one.
--
--   Differences from the source:
--   - encoding: a set J of jobs (a_i, d_i, w_i) with w_i > 0 and a_i < d_i (Section 8.1) → Finset Job with a natural-number label; ValidInstance J (nonempty, a < d, 0 < w); times in ℝ; reason: the base mission's published convention; labels only allow repeated triples
--   - encoding: f̂^λ_J, the optimal weighted objective value → weightedOptVal: sSup of v ≥ 0 such that some rate schedule gives every job λ_j f_j ≥ v (not capped at 1); reason: the optimum over feasible schedules; rate schedules do not exceed it (Lemma 5.1 uses only interval capacities)
--   - reading: serves the earliest-deadline … job …, with ties between equal deadlines broken arbitrarily (p.24) → a fixed strict total order ≺ refining deadlines, the rule quantified over every such ≺; reason: the proof uses one fixed order (Definition 5.4 "under the fixed tie-breaking rule"; Lemma 5.6 "the same strict total order"); decision 3 of SUPPLEMENT.md
--   - encoding: WeightedScaledEDF(1/2) is a … deterministic online algorithm → for every ≺ there is a causal WeightedOnlineAlg (weights revealed at arrival) whose schedule on every valid instance with positive weights is a run for ≺; reason: the base goal's convention for the existence clause
--   - reading: eligible jobs: c_i(t) < θ_i(t), released → also t < d_j; reason: as in the base mission; work after the deadline does not count
--   - encoding: 1/2-competitive: min_j λ_j c_j/w_j ≥ ½ f̂^λ_J → every run gives every job λ_j · frac r j ≥ ½ · weightedOptVal λ J; reason: frac caps the work at w_j; same values
--   - encoding: the arithmetic RAM model: arithmetic operations, comparisons, assignments and memory accesses take O(1) time (p.40) → the published unit-cost real RAM BlottoFPTAS.Main.RealRAM (exact + − × ÷, comparisons, rational literals, indirect memory, no floor or logarithm), Admissible ∧ Deterministic, cost = executed instructions; reason: it is that model; the bounds are strongly polynomial as in the paper
--   - encoding: jobs arrive online; jobs sharing an arrival time form one batch (p.40) → the instance is presented as a list L; batches L in increasing arrival time; one persistent machine run, each operation resumed from the previous state (runOp, driverStep); reason: the paper's online interaction; the batch order does not depend on the presentation
--   - reading: WeightedScaledEDF can be implemented → for every α′ > 0 given as an input real, every valid instance with λ_j > 0 and every presentation L, the event-driven run finishes and the assembled schedule is a WeightedScaledEDF(α′) run for the order (d_j, position in L); reason: an implementation must produce the algorithm's schedule; α′ is an input of ScaledEDF (p.3), and the paper fixes only α′ > 0 ("Fix some α′ > 0", Section 4, p.14); ties by index as in §8.1.7
--   - reading: worst-case O(log³ n) time per job arrival → every operation with k arriving jobs costs ≤ C(k + 1)log³(n + 2) (internal events: k = 0), and the run has ≤ C(n + 1) operations; reason: decision 4 of SUPPLEMENT.md: §8.1.7 bounds each batch by O(k log³ n), each event by O(log n) and the number of events by O(n); without bounds on events, arrival work could be moved to events
--   - encoding: O(f(n)) → ≤ C · f with one absolute C > 0 fixed before the instance, log n written as log(n + 2); reason: standard reading of O(·); log(n + 2) keeps the bound positive at n = 1
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Theorem 1.2, p.3 (PDF p.5); Section 5, pp.23–27 (PDF pp.25–29); Section 8.1.8, p.51 (PDF p.53)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_RealRAM
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_ValidInstance
import Definitions.Def_MaxMinFracSched_frac
import Definitions.Def_MaxMinFracSched_Supplement_weightedOptVal
import Definitions.Def_MaxMinFracSched_Supplement_IsWeightedScaledEDF
import Definitions.Def_MaxMinFracSched_Supplement_WeightedOnlineAlg
import Definitions.Def_MaxMinFracSched_Supplement_DriverState
import Definitions.Def_MaxMinFracSched_Supplement_driverInit
import Definitions.Def_MaxMinFracSched_Supplement_driverStep
import Definitions.Def_MaxMinFracSched_Supplement_segSchedule
import Definitions.Def_MaxMinFracSched_Supplement_inputOrder

namespace MaxMinFracSched

namespace Supplement

open BlottoFPTAS.Main.RealRAM

/-- **Theorem 1.2 (WeightedScaledEDF).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Theorem 1.2, p.3 (PDF p.5): "WeightedScaledEDF(1/2) is a 1/2-competitive deterministic online algorithm
for the weighted max-min fractional scheduling problem. WeightedScaledEDF can be implemented with
worst-case O(log3 n) time per job arrival." Proved in Section 5, pp.23–27 (PDF pp.25–29), and
Section 8.1.8, p.51 (PDF p.53).

Two parts.
1. *Competitive ratio.* For every strict total order `≺` on jobs that refines the deadline order:
   (a) there is a deterministic weighted online algorithm whose schedule on every valid instance
   with positive weights is a WeightedScaledEDF(1/2) run for `≺`; (b) every WeightedScaledEDF(1/2)
   run for `≺` on every valid instance `J` with weights `λ_j > 0` gives every job value
   `λ_j · f_j ≥ ½ · f̂^λ_J`.
2. *Implementation.* There is one admissible deterministic real-RAM program and one `C > 0` such
   that for every `α′ > 0` (Section 4, p.14: "Fix some α′ > 0"), every valid `J` with positive weights and every presentation `L`,
   the event-driven run (each job encoded as `[d_j, w_j, λ_j]`) finishes without failure, its
   schedule is a WeightedScaledEDF(α′) run for the order by deadline and then input position, it
   performs at most `C · (n + 1)` operations, and every operation with `k` arriving jobs takes at most
   `C · (k + 1) · log³(n + 2)` instructions.

**Formalization Note.** `f̂^λ_J` is the uncapped weighted optimum over feasible schedules. Ties
are broken by one fixed order, as in the proof (Definition 5.4, Lemma 5.6). The cost model is that
of `theorem_1_1_implementation`. -/
theorem theorem_1_2 :
    (∀ (prec : Job → Job → Prop) [IsStrictTotalOrder Job prec],
      (∀ j k : Job, j.d < k.d → prec j k) →
      (∃ A : WeightedOnlineAlg, ∀ (lam : Job → ℝ) (J : Finset Job), ValidInstance J →
        (∀ j ∈ J, 0 < lam j) → IsWeightedScaledEDF (1 / 2) lam prec J (A.sched lam J)) ∧
      (∀ (lam : Job → ℝ) (J : Finset Job), ValidInstance J → (∀ j ∈ J, 0 < lam j) →
        ∀ r, IsWeightedScaledEDF (1 / 2) lam prec J r →
          ∀ j ∈ J, (1 / 2 : ℝ) * weightedOptVal lam J ≤ lam j * frac r j)) ∧
    (∃ P : Program, Admissible P ∧ Deterministic P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (α' : ℝ), 0 < α' → ∀ (lam : Job → ℝ) (J : Finset Job) (L : List Job),
        ValidInstance J → (∀ j ∈ J, 0 < lam j) → L.Nodup → L.toFinset = J →
        ∃ (N : ℕ) (σ : DriverState),
          σ = (driverStep P (fun j => [j.d, j.w, lam j]) α' L)^[N] driverInit ∧
          σ.finished = true ∧ σ.failed = false ∧
          IsWeightedScaledEDF α' lam (inputOrder L) J (segSchedule σ.segs) ∧
          (σ.ops.length : ℝ) ≤ C * ((J.card : ℝ) + 1) ∧
          ∀ p ∈ σ.ops, (p.2 : ℝ) ≤ C * ((p.1 : ℝ) + 1) * Real.log ((J.card : ℝ) + 2) ^ 3) := by sorry

end Supplement

end MaxMinFracSched
