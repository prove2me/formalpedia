-- Prove2me | Theorems.Thm_OAI_Erdos3_affineMandatoryPrimes_outside_inverse
-- name    : OAI.Erdos3.affineMandatoryPrimes_outside_inverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:22:03.047083+00:00
-- url     : https://prove2.me/theorems/1be4c2d5-57b2-4c2f-b261-b18573d3d4b2
-- title:
--   Primes outside a superset of the mandatory primes have reciprocal at most the contraction
-- statement:
--   Let $\iota$ be a finite type, $\mathrm{prime} : \iota \to \mathbb{N}$ any function, and $\xi, P$ real numbers with $0 \le P$. Let $K$ be a finite subset of $\iota$ containing `affineMandatoryPrimes prime ξ P` (the set of $i$ with $\mathrm{prime}(i) \le$ `affineComparisonPrimeThreshold ξ P`, a real threshold defined by OpenAI), and let $i \in \iota$ with $i \notin K$. Then $\mathrm{prime}(i)^{-1} \le$ `affineComparisonContraction ξ P` (the reciprocal of `affineComparisonPrimeThreshold ξ P`), the inverse taken in $\mathbb{R}$.
--
--   Lean: `OAI.Erdos3.affineMandatoryPrimes_outside_inverse` in `lean/OAI/Combinatorics/Progressions/Lattices/PrimeCoordinateCells.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/PrimeCoordinateCells.lean#L298

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem affineMandatoryPrimes_outside_inverse {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) {ξ P : ℝ} (hP : 0 ≤ P) (K : Finset ι)
    (hK : affineMandatoryPrimes prime ξ P ⊆ K) (i : ι) (hi : i ∉ K) :
    (prime i : ℝ)⁻¹ ≤ affineComparisonContraction ξ P := by
  sorry

end Erdos3
end
end OAI
