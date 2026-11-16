-- Prove2me | Theorems.Thm_MaxMinFracSched_Supplement_theorem_1_4
-- name    : MaxMinFracSched.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:26:53.131896+00:00
-- url     : https://prove2.me/theorems/44e8e728-c788-4208-a2fb-e95e535928e5
-- title:
--   Theorem 1.4 — a deterministic $O(n\log^2 n)$ real-RAM algorithm computes $\rho^\star$ and $\hat f$ exactly
-- statement:
--   Let $J$ be a valid instance of $n$ jobs. Its maximum density is $\rho^\star_J=\max_{L<R}W_J([L,R])/(R-L)$, where $W_J([L,R])$ is the total work of the jobs whose windows lie in $[L,R]$, and its offline optimum $\hat f_J$ is the largest minimum fractional completion a feasible schedule achieves.
--
--   **Theorem.** There are one deterministic program $P$ for the unit-cost real RAM (exact arithmetic and comparisons, unit cost per instruction) and one constant $C>0$ such that for every valid instance $J$ of $n$ jobs, given in any order as the $3n$ reals $a_j,d_j,w_j$, the program halts within
--   $$
--   C\,n\log^2(n+2)
--   $$
--   instructions and outputs exactly the pair $(\rho^\star_J,\hat f_J)$.
--
--   The best previous algorithm for computing $\rho^\star$ took $O(n^2)$ time; this one is also strongly polynomial, since its number of operations does not depend on the magnitudes of the input reals.
--
--   Differences from the source:
--   - encoding: a set J of jobs (a_i, d_i, w_i) with w_i > 0 and a_i < d_i (Section 8.1) → Finset Job with a natural-number label; ValidInstance J (nonempty, a < d, 0 < w); times in ℝ; reason: the base mission's published convention; labels only allow repeated triples
--   - encoding: the arithmetic RAM model: arithmetic operations, comparisons, assignments and memory accesses take O(1) time (p.40) → the published unit-cost real RAM BlottoFPTAS.Main.RealRAM (exact + − × ÷, comparisons, rational literals, indirect memory, no floor or logarithm), Admissible ∧ Deterministic, cost = executed instructions; reason: it is that model; the bounds are strongly polynomial as in the paper
--   - encoding: an offline algorithm that computes ρ⋆ and thus f̂ → input: the 3n reals a_j, d_j, w_j of the jobs in any order (after the length); output exactly [maxDensity J, optVal J]; reason: the input in the machine's layout; both values are required
--   - encoding: O(f(n)) → ≤ C · f with one absolute C > 0 fixed before the instance, log n written as log(n + 2); reason: standard reading of O(·); log(n + 2) keeps the bound positive at n = 1
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Theorem 1.4, p.4 (PDF p.6); restated and proved pp.51–53 (PDF pp.53–55); model p.40 (PDF p.42)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_RealRAM
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_ValidInstance
import Definitions.Def_MaxMinFracSched_optVal
import Definitions.Def_MaxMinFracSched_maxDensity

namespace MaxMinFracSched

namespace Supplement

open BlottoFPTAS.Main.RealRAM

/-- **Theorem 1.4 (offline computation of `ρ⋆` and `f̂`).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Theorem 1.4, p.4 (PDF p.6; restated and proved pp.51–53, PDF pp.53–55): "There is a
deterministic O(n log2 n)-time offline algorithm that computes ρ⋆ and thus the objective value f̂
for the max-min fractional scheduling problem." Model: p.40 (PDF p.42), "arithmetic operations,
comparisons, assignments, and memory accesses take O(1) time".

There is one admissible deterministic real-RAM program `P` and one constant `C > 0` such that for
every valid instance `J` of `n` jobs, given in any order `L` as the `3n` reals `a_j, d_j, w_j`
(after the input length), `P` halts within `C · n · log²(n + 2)` instructions and outputs exactly
`[ρ⋆_J, f̂_J]`.

**Formalization Note.** The published unit-cost real RAM (exact `+ − × ÷`, comparisons, rational
literals, indirect memory; no floor or logarithm), so the algorithm is strongly polynomial as the
paper's is. `C` is fixed before `J`. -/
theorem theorem_1_4 :
    ∃ P : Program, Admissible P ∧ Deterministic P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (J : Finset Job) (L : List Job), ValidInstance J → L.Nodup → L.toFinset = J →
        output P (L.flatMap (fun j => [j.a, j.d, j.w])) zeroTape = some [maxDensity J, optVal J] ∧
        HaltsWithin P (L.flatMap (fun j => [j.a, j.d, j.w])) zeroTape
          (C * (J.card : ℝ) * Real.log ((J.card : ℝ) + 2) ^ 2) := by sorry

end Supplement

end MaxMinFracSched
