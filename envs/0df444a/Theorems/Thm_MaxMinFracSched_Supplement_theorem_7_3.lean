-- Prove2me | Theorems.Thm_MaxMinFracSched_Supplement_theorem_7_3
-- name    : MaxMinFracSched.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:27:44.469197+00:00
-- url     : https://prove2.me/theorems/44685884-df76-493a-958f-7afd49e49630
-- title:
--   Theorem 7.3 — densest-interval decomposition of the lexicographic optimum
-- statement:
--   Let $J$ be a valid instance whose jobs carry pairwise distinct labels, let $\rho^\star_J$ be its maximum density, let $I^\star$ be the set of its densest intervals, and let $S_J(I^\star)$ be the jobs whose windows lie inside a densest interval. The contracted instance $J-I^\star$ deletes the jobs of $S_J(I^\star)$ and contracts every densest interval to a point. For a lexicographically optimal schedule $r$, write $\hat f_{J,i}=f_i(r)$.
--
--   **Theorem.**
--
--   1. $J$ has a lexicographically optimal schedule.
--   2. If $\rho^\star_J\le1$, then $\hat f_{J,i}=1$ for every $i\in J$.
--   3. If $\rho^\star_J>1$, set $\beta=1/\rho^\star_J$. Then $J-I^\star$ has a lexicographically optimal schedule, and
--   $$
--   \hat f_{J,i}=\begin{cases}\beta, & i\in S_J(I^\star),\\ \hat f_{J-I^\star,i'}, & i\notin S_J(I^\star),\end{cases}
--   $$
--   where $i'$ is the job corresponding to $i$ in $J-I^\star$. Moreover $\hat f_{J-I^\star,i'}>\beta$ for every job $i'$ of $J-I^\star$.
--
--   All equalities hold for every lexicographically optimal schedule of $J$ and of $J-I^\star$, so the benchmark vector is unique (Corollary 7.4). Applying the theorem again to $J-I^\star$ gives the paper's equivalent description: repeatedly remove the jobs inside the densest intervals, give them the reciprocal of the current maximum density, contract those intervals, and give fraction $1$ to every job left once the maximum density is at most $1$.
--
--   Differences from the source:
--   - encoding: a nonempty instance J with jobs indexed by i ∈ J → ValidInstance J (nonempty, a < d, 0 < w) with pairwise distinct labels (Set.InjOn Job.id J); reason: validity is the paper's standing assumption (Section 8.1, p.40); jobs are indexed by i in the paper, and any instance can be relabeled, so distinct labels exclude nothing; decision 5 of SUPPLEMENT.md
--   - reading: I⋆ the set of densest intervals; the contracted instance J − I⋆ → all densest intervals; J − I⋆ deletes S_J(I⋆) and maps the other jobs by t ↦ t − |U ∩ (−∞, t]|, U the union of all densest intervals, keeping the label; reason: Definition 7.2 contracts one interval; the maximal densest intervals are disjoint and separated by gaps, so contracting them one by one gives this map; decision 5
--   - encoding: f̂_{J,i}, the lexicographic benchmark fraction of job i → frac r i for every lexicographically optimal rate schedule r; existence of such r for J and for J − I⋆ is part of the conclusion; reason: the benchmark presupposes a lex-optimal schedule; stating the equalities for every one is the paper's uniqueness (Corollary 7.4); rate schedules satisfy the same interval capacities, so the optimum is the same
--   - encoding: the "Equivalently …" paragraph → not a separate clause; reason: it is the recursion given by applying clauses 2–3 to J − I⋆
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Theorem 7.3, pp.33–34 (PDF pp.35–36); Definition 7.2, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_ValidInstance
import Definitions.Def_MaxMinFracSched_frac
import Definitions.Def_MaxMinFracSched_maxDensity
import Definitions.Def_MaxMinFracSched_Supplement_IsLexOpt
import Definitions.Def_MaxMinFracSched_Supplement_densestCovered
import Definitions.Def_MaxMinFracSched_Supplement_contractMap
import Definitions.Def_MaxMinFracSched_Supplement_contract

namespace MaxMinFracSched

namespace Supplement

/-- **Theorem 7.3 (densest-interval decomposition).** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Theorem 7.3, pp.33–34 (PDF pp.35–36): "Let J be a nonempty instance, and let I⋆ be the set
of densest intervals of J and let ρ⋆J be the density of these densest intervals. … If ρ⋆J ≤ 1, then
f̂J,i = 1 for every i ∈ J. Otherwise, set β := 1/ρ⋆J … f̂J,i = β for i ∈ SJ(I⋆), f̂J−I⋆,i for
i ∉ SJ(I⋆) … In particular, every job of J−I⋆ has benchmark fraction strictly greater than β."

For a valid instance `J` whose jobs have pairwise distinct labels:
1. `J` has a lexicographically optimal schedule;
2. if `ρ⋆_J ≤ 1`, every lexicographically optimal schedule gives every job fraction `1`;
3. if `ρ⋆_J > 1`, with `β = 1/ρ⋆_J`: the contracted instance `J − I⋆` has a lexicographically optimal
   schedule; every lexicographically optimal schedule of `J` gives every job of `S_J(I⋆)` fraction
   `β`; for every lexicographically optimal `r` of `J` and `r'` of `J − I⋆`, every job `i ∉ S_J(I⋆)`
   has `f_i(r) = f_{i'}(r')` for its corresponding job `i'`; and every job of `J − I⋆` has fraction
   greater than `β` under every lexicographically optimal schedule of `J − I⋆`.

**Formalization Note.** `I⋆` is the set of all densest intervals and `J − I⋆` contracts their
union. Distinct labels encode the paper's job indices `i ∈ J`, so the label-preserving contraction
does not merge jobs. Stating the conclusions for every lexicographically optimal schedule also
gives the uniqueness of the vector `(f̂_{J,i})` (Corollary 7.4). The "Equivalently …" paragraph is
the recursion obtained by applying the theorem again to `J − I⋆`. -/
theorem theorem_7_3 (J : Finset Job) (hJ : ValidInstance J)
    (hid : Set.InjOn Job.id (J : Set Job)) :
    (∃ r, IsLexOpt J r) ∧
    (maxDensity J ≤ 1 → ∀ r, IsLexOpt J r → ∀ i ∈ J, frac r i = 1) ∧
    (1 < maxDensity J →
      (∃ r', IsLexOpt (contract J) r') ∧
      (∀ r, IsLexOpt J r → ∀ i ∈ densestCovered J, frac r i = 1 / maxDensity J) ∧
      (∀ r r', IsLexOpt J r → IsLexOpt (contract J) r' →
        ∀ i ∈ J, i ∉ densestCovered J → frac r i = frac r' (contractMap J i)) ∧
      (∀ r', IsLexOpt (contract J) r' → ∀ i ∈ contract J, 1 / maxDensity J < frac r' i)) := by sorry

end Supplement

end MaxMinFracSched
