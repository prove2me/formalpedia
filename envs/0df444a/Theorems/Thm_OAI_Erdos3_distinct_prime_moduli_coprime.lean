-- Prove2me | Theorems.Thm_OAI_Erdos3_distinct_prime_moduli_coprime
-- name    : OAI.Erdos3.distinct_prime_moduli_coprime
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:16:22.661526+00:00
-- url     : https://prove2.me/theorems/32e39dfc-23cf-41ef-b2d1-30796bbe516a
-- title:
--   Distinct prime moduli are pairwise coprime
-- statement:
--   Let $J$ be a type and $N : J \to \mathbb{N}$ a function such that $N(j)$ is prime for every $j\in J$ and $N$ is injective. Then the values of $N$ are pairwise coprime: for all $i\ne j$ in $J$, $\gcd(N(i),N(j))=1$.
--
--   Lean: `OAI.Erdos3.distinct_prime_moduli_coprime` in `lean/OAI/Combinatorics/Progressions/Lattices/AbsoluteCRTWindow.lean` (OpenAI); the statement uses only Mathlib definitions.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AbsoluteCRTWindow.lean#L16

import Mathlib
import Definitions.Def_ErdosReciprocal

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem distinct_prime_moduli_coprime {J : Type*} (N : J → ℕ)
    (hprime : ∀ j, (N j).Prime) (hinj : Function.Injective N) :
    Pairwise (fun i j => Nat.Coprime (N i) (N j)) := by
  sorry

end Erdos3
end
end OAI
