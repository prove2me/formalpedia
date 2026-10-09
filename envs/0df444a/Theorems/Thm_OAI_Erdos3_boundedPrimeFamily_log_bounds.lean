-- Prove2me | Theorems.Thm_OAI_Erdos3_boundedPrimeFamily_log_bounds
-- name    : OAI.Erdos3.boundedPrimeFamily_log_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:16:36.705804+00:00
-- url     : https://prove2.me/theorems/ef0269c9-84a1-4a21-a100-c9856e3ffce2
-- title:
--   The primes up to Q and their maximal powers up to Q are bounded by e^P when Q is
-- statement:
--   Let $Q$ be a natural number and $P$ a real number with $Q \le e^{P}$. `BoundedPrime Q` is the type of primes $p \le Q$ (the subtype of `boundedPrimes Q`, the primes in $\{0, \dots, Q\}$), and `boundedPrimePower Q p` $= p^{\lfloor \log_p Q \rfloor}$ (the exponent being Mathlib's `Nat.log p Q`). Then the number of primes $p \le Q$ is at most $e^{P}$, and for every such prime $p$, `boundedPrimePower Q p` $\le e^{P}$.
--
--   Lean: `OAI.Erdos3.boundedPrimeFamily_log_bounds` in `lean/OAI/Combinatorics/Progressions/Lattices/PrimeFamilyCutoff.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/PrimeFamilyCutoff.lean#L85

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem boundedPrimeFamily_log_bounds (Q : ℕ) {P : ℝ} (hQ : (Q : ℝ) ≤ Real.exp P) :
    (Fintype.card (BoundedPrime Q) : ℝ) ≤ Real.exp P ∧
      ∀ p : BoundedPrime Q, (boundedPrimePower Q p : ℝ) ≤ Real.exp P := by
  sorry

end Erdos3
end
end OAI
