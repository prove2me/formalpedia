-- Prove2me | Theorems.Thm_OAI_Erdos3_selectedCombined_coprime_outside
-- name    : OAI.Erdos3.selectedCombined_coprime_outside
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:16:30.731735+00:00
-- url     : https://prove2.me/theorems/c7fb720c-1f33-4cd1-a50b-db4a3d7be307
-- title:
--   lcm(M, ∏_{i∈K} q_i) is coprime to q_j for j outside K
-- statement:
--   Let $\iota$ be a type with decidable equality and $q:\iota\to\mathbb{N}$ a family whose values are pairwise coprime ($\gcd(q_i,q_j)=1$ for $i\ne j$). Let $M$ be a natural number and $K\subseteq\iota$ a finite set such that $\gcd(M,q_i)=1$ for every $i\notin K$. Then for every $j\in\iota$ with $j\notin K$,
--   $$\gcd\Big(\operatorname{lcm}\big(M,\textstyle\prod_{i\in K}q_i\big),\,q_j\Big)=1.$$
--
--   Lean: `OAI.Erdos3.selectedCombined_coprime_outside` in `lean/OAI/Combinatorics/Progressions/Estimates/StableReferenceMean.lean` (OpenAI); the statement uses only Mathlib definitions.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/StableReferenceMean.lean#L20

import Mathlib
import Definitions.Def_ErdosReciprocal

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedCombined_coprime_outside {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (hpair : Pairwise (fun i j => (q i).Coprime (q j))) (M : ℕ) (K : Finset ι)
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (j : ι) (hj : j ∉ K) :
    (M.lcm (∏ i ∈ K, q i)).Coprime (q j) := by
  sorry

end Erdos3
end
end OAI
