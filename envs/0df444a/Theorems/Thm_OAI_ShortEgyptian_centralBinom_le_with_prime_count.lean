-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_centralBinom_le_with_prime_count
-- name    : OAI.ShortEgyptian.centralBinom_le_with_prime_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:55:33.894224+00:00
-- url     : https://prove2.me/theorems/a50566bf-0f0e-44bf-8bf4-343571491a5a
-- title:
--   Upper bound for $\binom{2n}{n}$ in terms of the number of primes in $(n,2n]$
-- statement:
--   For a natural number $n$ let $\Pi_n=\{p \text{ prime}: n<p\le 2n\}$ be the set of primes in the dyadic interval $(n,2n]$. For every natural number $n>2$,
--
--   $$
--   \binom{2n}{n}\;\le\;(2n)^{\lfloor\sqrt{2n}\rfloor}\cdot 4^{\lfloor 2n/3\rfloor}\cdot(2n)^{|\Pi_n|}.
--   $$
--
--   This is the upper half of the classical elementary argument for Bertrand's postulate. Combined with the lower bound $\binom{2n}{n}\ge 4^n/(2n+1)$ and after taking logarithms, it shows that $(n,2n]$ contains at least $c\,n/\log n$ primes for some absolute $c>0$ and all large $n$. In this way it provides a supply of primes in dyadic intervals.
--
--   **Formalization Note** In Lean, $\lfloor\sqrt{2n}\rfloor$ is `Nat.sqrt (2*n)`, $\lfloor 2n/3\rfloor$ is the natural-number division `2*n/3`, $\binom{2n}{n}$ is `n.centralBinom`, and $\Pi_n$ is `dyadicPrimes n`, defined as the primes in `Ioc n (2*n)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/PrimeLists.lean#L10-L72

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists

open OAI OAI.ShortEgyptian
open Finset

theorem OAI.ShortEgyptian.centralBinom_le_with_prime_count (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^Nat.sqrt (2*n)*4^(2*n/3)*(2*n)^(dyadicPrimes n).card := by sorry
