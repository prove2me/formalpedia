-- Prove2me | Theorems.Thm_MaxMinFracSched_Supplement_theorem_1_1_implementation
-- name    : MaxMinFracSched.Supplement.theorem_1_1_implementation
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:23:58.376962+00:00
-- url     : https://prove2.me/theorems/424863bc-cda5-4079-a41d-b16dc3c5860c
-- title:
--   Theorem 1.1 (third sentence) — ScaledEDF$(\alpha^{\prime})$ has an exact event-driven real-RAM implementation with worst-case $O(\log^3 n)$ time per job arrival
-- statement:
--   Consider the unit-cost real RAM of Section 8 (p.40): arithmetic operations, comparisons, assignments and memory accesses take unit time. Run a program persistently on an instance presented online: jobs sharing an arrival time arrive as one batch, each job given by the reals $(d_j,w_j)$ after the batch's arrival time and the parameter $\alpha'$. Between arrivals the program may announce internal events (a job reaching its target, a deadline passing). After every operation it says which job it serves from then on, or that it idles.
--
--   **Theorem.** There are one deterministic real-RAM program $P$ and one constant $C>0$ such that for every $\alpha'>0$, every valid instance $J$ of $n$ jobs and every presentation of $J$, the event-driven run of $P$ finishes after finitely many operations, none of which fails to halt, and
--
--   1. the schedule assembled from its decisions is a ScaledEDF$(\alpha')$ run on $J$: at almost every time $t$ it serves an eligible job of earliest deadline, eligible meaning released, unexpired and with $c_j(t)<\alpha'\hat f_J(t)w_j$, and idles when there is none;
--   2. the run has at most $C(n+1)$ operations;
--   3. every operation with $k$ arriving jobs (with $k=0$ for an internal event) executes at most
--   $$
--   C\,(k+1)\,\log^3(n+2)
--   $$
--   instructions.
--
--   With $\alpha'=1/2$ this is the third sentence of Theorem 1.1: the $1/2$-competitive algorithm ScaledEDF$(1/2)$ of the published goal can be run with worst-case polylogarithmic time per arrival.
--
--   Differences from the source:
--   - encoding: a set J of jobs (a_i, d_i, w_i) with w_i > 0 and a_i < d_i (Section 8.1) → Finset Job with a natural-number label; ValidInstance J (nonempty, a < d, 0 < w); times in ℝ; reason: the base mission's published convention; labels only allow repeated triples
--   - encoding: the arithmetic RAM model: arithmetic operations, comparisons, assignments and memory accesses take O(1) time (p.40) → the published unit-cost real RAM BlottoFPTAS.Main.RealRAM (exact + − × ÷, comparisons, rational literals, indirect memory, no floor or logarithm), Admissible ∧ Deterministic, cost = executed instructions; reason: it is that model; the bounds are strongly polynomial as in the paper
--   - encoding: jobs arrive online; jobs sharing an arrival time form one batch (p.40) → the instance is presented as a list L; batches L in increasing arrival time; one persistent machine run, each operation resumed from the previous state (runOp, driverStep); reason: the paper's online interaction; the batch order does not depend on the presentation
--   - reading: ScaledEDF can be implemented → for every α′ > 0 given as an input real, on every valid instance and presentation, the event-driven run finishes and the assembled schedule is an IsScaledEDF α′ run; reason: an implementation must produce the algorithm's schedule; α′ is an input of ScaledEDF (p.3), and the paper fixes only α′ > 0 ("Fix some α′ > 0", Section 4, p.14); ties by index as in §8.1.7
--   - reading: worst-case O(log³ n) time per job arrival → every operation with k arriving jobs costs ≤ C(k + 1)log³(n + 2) (internal events: k = 0), and the run has ≤ C(n + 1) operations; reason: decision 4 of SUPPLEMENT.md: §8.1.7 bounds each batch by O(k log³ n), each event by O(log n) and the number of events by O(n); without bounds on events, arrival work could be moved to events
--   - encoding: O(f(n)) → ≤ C · f with one absolute C > 0 fixed before the instance, log n written as log(n + 2); reason: standard reading of O(·); log(n + 2) keeps the bound positive at n = 1
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Theorem 1.1, p.3 (PDF p.5); Section 8.1.7, pp.50–51 (PDF pp.52–53); model p.40 (PDF p.42)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_RealRAM
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_ValidInstance
import Definitions.Def_MaxMinFracSched_IsScaledEDF
import Definitions.Def_MaxMinFracSched_Supplement_DriverState
import Definitions.Def_MaxMinFracSched_Supplement_driverInit
import Definitions.Def_MaxMinFracSched_Supplement_driverStep
import Definitions.Def_MaxMinFracSched_Supplement_segSchedule

namespace MaxMinFracSched

namespace Supplement

open BlottoFPTAS.Main.RealRAM

/-- **Theorem 1.1, third sentence (implementation of ScaledEDF).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Theorem 1.1, p.3 (PDF p.5): "ScaledEDF can be implemented with worst-case O(log3 n) time per
job arrival"; proved in Section 8.1.7, pp.50–51 (PDF pp.52–53), in the model of p.40 (PDF p.42):
"arithmetic operations, comparisons, assignments, and memory accesses take O(1) time".

There is one admissible deterministic real-RAM program `P` and one constant `C > 0` such that for
every `α′ > 0` (an input of the program; Section 4, p.14, PDF p.16: "Fix some α′ > 0"), every valid instance `J` and every presentation `L` of
its jobs, the event-driven run of `P` (`driverStep`, each job encoded as `[d_j, w_j]`) finishes after
finitely many operations without a failure, and
1. the schedule assembled from its decisions is a ScaledEDF(α′) run on `J`;
2. it performs at most `C · (n + 1)` operations, `n = |J|`;
3. every operation takes at most `C · (k + 1) · log³(n + 2)` instructions, where `k` is the number of
   jobs arriving with it (`k = 0` for an internal event).

**Formalization Note.** The machine is the published unit-cost real RAM (exact `+ − × ÷`,
comparisons, rational literals, indirect memory; no floor, no logarithm), run persistently across
operations. `C` is fixed before `α′`, `J` and `L`. `log(n + 2)` keeps the bound positive at `n = 1`. -/
theorem theorem_1_1_implementation :
    ∃ P : Program, Admissible P ∧ Deterministic P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (α' : ℝ), 0 < α' → ∀ (J : Finset Job) (L : List Job),
        ValidInstance J → L.Nodup → L.toFinset = J →
        ∃ (N : ℕ) (σ : DriverState),
          σ = (driverStep P (fun j => [j.d, j.w]) α' L)^[N] driverInit ∧
          σ.finished = true ∧ σ.failed = false ∧
          IsScaledEDF α' J (segSchedule σ.segs) ∧
          (σ.ops.length : ℝ) ≤ C * ((J.card : ℝ) + 1) ∧
          ∀ p ∈ σ.ops, (p.2 : ℝ) ≤ C * ((p.1 : ℝ) + 1) * Real.log ((J.card : ℝ) + 2) ^ 3 := by sorry

end Supplement

end MaxMinFracSched
