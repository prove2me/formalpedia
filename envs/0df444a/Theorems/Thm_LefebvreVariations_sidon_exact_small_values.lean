-- Prove2me | Theorems.Thm_LefebvreVariations_sidon_exact_small_values
-- name    : LefebvreVariations.sidon_exact_small_values
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:05:24.784554+00:00
-- url     : https://prove2.me/theorems/69ab0519-bed2-49a1-b8eb-f716cbab6252
-- title:
--   Lefebvre's variations, No. 143 — on a theme by Erdős: exact values of the Sidon-set function h(N) at N = 25, 26, 34, 35, 44, 45
-- statement:
--   Let $h(N)$ be the largest size of a Sidon set in $\{1,\dots,N\}$. Then
--   $$h(25)=6,\quad h(26)=7,\quad h(34)=7,\quad h(35)=8,\quad h(44)=8,\quad h(45)=9 .$$
--
--   These are the places where $h$ jumps. A Sidon set with $m$ elements and diameter $\ell$ is an $m$-mark Golomb ruler of length $\ell$, and optimal rulers with $6,7,8,9,10$ marks have lengths $17,25,34,44,55$; hence $h$ first reaches $7,8,9$ at $N=26,35,45$ and not before.
--
--   This is the exact small-value table behind Erdős Problem 30 on the maximal size of Sidon sets in $\{1,\dots,N\}$.
--
--   **Formalization Note** `Erdos30.h N` is the maximum cardinality of a subset of `Finset.Icc 1 N` that is Sidon in the sense of `Erdos30.IsSidon`, computed as a supremum over the powerset, in the platform definitions `Def_Erdos30Basic`. The statement is the conjunction of the six equalities. The upper bounds need the exhaustive optimality of the Golomb rulers; the lower bounds are explicit sets.
--
--   **Why this is a variation.** This is a variation of Erdős Problem 30 on the platform, the open question of whether $h(N)=\sqrt N+O(N^\varepsilon)$ for the largest Sidon set in $\{1,\dots,N\}$. It pins down exact small values of the parent's own function $h$ at the places where it jumps, a finite explicit computation. Such exact values are the calibration data any proposed asymptotic or structural result about $h$ must match.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Erdos Problem 30 (https://www.erdosproblems.com/30), Sidon sets in {1,...,N}. Optimal Golomb ruler lengths 17, 25, 34, 44, 55 for 6, 7, 8, 9, 10 marks: OEIS A003022 and the Golomb-ruler literature (exhaustive searches; authors and years cited from memory, not re-checked). All six values were also confirmed by an exhaustive depth-first search while preparing this statement. Origin: the platform problem Erdos30.erdos_30 (Open), at its exact small values of h(N).

import Definitions.Def_Erdos30Basic

set_option autoImplicit false

namespace LefebvreVariations

/-- Exact small values of the function `h` of Erdős Problem 30 (the maximum size of a Sidon
set in `{1,…,N}`) at the thresholds where it jumps: `h(25)=6`, `h(26)=7`, `h(34)=7`, `h(35)=8`,
`h(44)=8`, `h(45)=9`. A ruler with `m` marks and length `ℓ` is a Sidon set in `{1,…,ℓ+1}`, so the jumps sit at
`N = ℓ+1`; the optimal Golomb rulers with `6,7,8,9,10` marks have lengths `17, 25, 34, 44, 55`,
and exactness is the exhaustive search of the Golomb-ruler literature (OEIS A003022; Shearer, Robinson–Bernstein, cited from memory).
Source: Erdős Problem 30 (https://www.erdosproblems.com/30). -/
theorem sidon_exact_small_values :
    Erdos30.h 25 = 6 ∧ Erdos30.h 26 = 7 ∧ Erdos30.h 34 = 7 ∧ Erdos30.h 35 = 8 ∧
      Erdos30.h 44 = 8 ∧ Erdos30.h 45 = 9 := by
  sorry

end LefebvreVariations
