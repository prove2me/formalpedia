-- Prove2me | Theorems.Thm_MaxMinFracSched_Supplement_theorem_8_1
-- name    : MaxMinFracSched.Supplement.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:28:36.486042+00:00
-- url     : https://prove2.me/theorems/acd2554d-a63d-4ca7-8763-d71b56b22314
-- title:
--   Theorem 8.1 — $\rho^\star(t)$ and $\hat f(t)$ maintained exactly under batched arrivals in $O(n\log^3 n)$ total time, $O(n\log^2 n)$ space, $O(k\log^3 n)$ per batch
-- statement:
--   Let $J$ be a valid instance of $n$ jobs, presented online in batches: all jobs with the same arrival time $a$ arrive together, as the reals $(a,d_{j_1},w_{j_1},\dots,d_{j_k},w_{j_k})$, and batches come in increasing order of arrival time. For a time $t$ let $\rho^\star(t)$ be the maximum density of the prefix instance $J_{\le t}$ of jobs released by $t$, and $\hat f(t)$ its offline optimum.
--
--   **Theorem.** There are one deterministic program $P$ for the unit-cost real RAM and one constant $C>0$ such that for every valid instance $J$ of $n$ jobs and every presentation, running $P$ persistently on the batches (each batch resumes from the state the previous one left), every batch halts and
--
--   1. after the batch with arrival time $a$ the program outputs exactly $(\rho^\star(a),\hat f(a))$;
--   2. that batch, of $k\ge1$ jobs, takes at most $C\,k\log^3(n+2)$ instructions;
--   3. all batches together take at most $C\,n\log^3(n+2)$ instructions;
--   4. at most $C\,n\log^2(n+2)$ distinct memory cells are written during the whole run.
--
--   This is the data structure behind the implementations of ScaledEDF and WeightedScaledEDF (Theorems 1.1 and 1.2).
--
--   Differences from the source:
--   - encoding: a set J of jobs (a_i, d_i, w_i) with w_i > 0 and a_i < d_i (Section 8.1) → Finset Job with a natural-number label; ValidInstance J (nonempty, a < d, 0 < w); times in ℝ; reason: the base mission's published convention; labels only allow repeated triples
--   - encoding: the arithmetic RAM model: arithmetic operations, comparisons, assignments and memory accesses take O(1) time (p.40) → the published unit-cost real RAM BlottoFPTAS.Main.RealRAM (exact + − × ÷, comparisons, rational literals, indirect memory, no floor or logarithm), Admissible ∧ Deterministic, cost = executed instructions; reason: it is that model; the bounds are strongly polynomial as in the paper
--   - encoding: jobs arrive online; jobs sharing an arrival time form one batch (p.40) → the instance is presented as a list L; batches L in increasing arrival time; one persistent machine run, each operation resumed from the previous state (runOp, driverStep); reason: the paper's online interaction; the batch order does not depend on the presentation
--   - encoding: ρ⋆(t) = max over L ∈ L(t), R ∈ R(t), L < R of ρ_{J≤t}([L, R]) (19), and f̂(t) → maxDensity (pre J a) (sup over all intervals) and optAt J a, output exactly after the batch arriving at a; reason: equal to (19) and to 1/max{1, ρ⋆(t)} by Corollary 3.4; between arrivals the values do not change
--   - reading: O(n log² n) space → at most C n log²(n + 2) distinct memory cells written by store instructions over the whole run; reason: registers are O(1) for a fixed program; input cells are written by the environment; obsolete versions count, as in the proof
--   - encoding: n, the number of job arrivals → n = |J|, the final number of jobs, in every bound; reason: as in the paper
--   - encoding: O(f(n)) → ≤ C · f with one absolute C > 0 fixed before the instance, log n written as log(n + 2); reason: standard reading of O(·); log(n + 2) keeps the bound positive at n = 1
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Theorem 8.1, p.40 (PDF p.42); proof Section 8.1.7, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_RealRAM
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_ValidInstance
import Definitions.Def_MaxMinFracSched_pre
import Definitions.Def_MaxMinFracSched_optAt
import Definitions.Def_MaxMinFracSched_maxDensity
import Definitions.Def_MaxMinFracSched_Supplement_runOps
import Definitions.Def_MaxMinFracSched_Supplement_batches
import Definitions.Def_MaxMinFracSched_Supplement_maintInput

namespace MaxMinFracSched

namespace Supplement

open BlottoFPTAS.Main.RealRAM

/-- **Theorem 8.1 (online maintenance of `ρ⋆(t)` and `f̂(t)`).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Theorem 8.1, p.40 (PDF p.42): "Over a sequence of n job arrivals, the maximum work
density ρ⋆(t), and hence f̂(t), can be maintained exactly in O(n log3 n) total time and O(n log2 n)
space. A batch of k ≥ 1 jobs arriving at a common time is processed in worst-case O(k log3 n)
time." Model: p.40, "arithmetic operations, comparisons, assignments, and memory accesses take O(1)
time".

There is one admissible deterministic real-RAM program `P` and one constant `C > 0` such that for
every valid instance `J` of `n` jobs and every presentation `L`, running `P` persistently on the
batches in increasing order of arrival time (batch `B` with arrival time `a` given as
`[a, d_{j₁}, w_{j₁}, …]`), every operation halts and
1. after the batch with arrival time `a`, the output is exactly `[ρ⋆(a), f̂(a)]`, with
   `ρ⋆(a) = maxDensity (J≤a)` and `f̂(a) = optAt J a`;
2. that batch of `k` jobs takes at most `C · k · log³(n + 2)` instructions;
3. all batches together take at most `C · n · log³(n + 2)` instructions;
4. at most `C · n · log²(n + 2)` distinct memory cells are written over the whole run.

**Formalization Note.** The machine starts in the published real RAM's initial state on the empty
input and keeps its state between batches (`runOps`). `C` is fixed before `J` and `L`; `n` is the
final number of jobs, as in the paper. Space counts the memory cells the program writes; registers
are `O(1)` for a fixed program. -/
theorem theorem_8_1 :
    ∃ P : Program, Admissible P ∧ Deterministic P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (J : Finset Job) (L : List Job), ValidInstance J → L.Nodup → L.toFinset = J →
        ∃ res : List (List ℝ × ℕ × Finset ℤ),
          runOps P (initState []) ((batches L).map maintInput) = some res ∧
          res.length = (batches L).length ∧
          (∀ x ∈ (batches L).zip res,
            x.2.1 = [maxDensity (pre J ((x.1.head?.map Job.a).getD 0)),
              optAt J ((x.1.head?.map Job.a).getD 0)] ∧
            (x.2.2.1 : ℝ) ≤ C * (x.1.length : ℝ) * Real.log ((J.card : ℝ) + 2) ^ 3) ∧
          (((res.map (fun x : List ℝ × ℕ × Finset ℤ => x.2.1)).sum : ℕ) : ℝ) ≤
            C * (J.card : ℝ) * Real.log ((J.card : ℝ) + 2) ^ 3 ∧
          ((((res.map (fun x : List ℝ × ℕ × Finset ℤ => x.2.2)).foldr (· ∪ ·) ∅).card : ℕ) : ℝ) ≤
            C * (J.card : ℝ) * Real.log ((J.card : ℝ) + 2) ^ 2 := by sorry

end Supplement

end MaxMinFracSched
