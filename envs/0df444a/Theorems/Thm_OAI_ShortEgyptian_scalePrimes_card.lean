-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_scalePrimes_card
-- name    : OAI.ShortEgyptian.scalePrimes_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:56:06.096642+00:00
-- url     : https://prove2.me/theorems/9a27be5f-19ea-42bc-8029-2f46e028b9f9
-- title:
--   At least $S^{99}$ primes lie in $(\lfloor S^{100}\rfloor, 2\lfloor S^{100}\rfloor]$
-- statement:
--   For a real number $S$ let $N_S=\lfloor S^{100}\rfloor$ and let
--   $$
--   \mathcal P_S=\{\,p \text{ prime} : N_S<p\le 2N_S\,\}
--   $$
--   be the set of primes in the dyadic interval $(N_S,2N_S]$. Here $\log$ is the natural logarithm. If $S\ge 2$, $\log S\ge 1$ and $4000\log S\le S$, then
--
--   $$
--   |\mathcal P_S|\ \ge\ S^{99}.
--   $$
--
--   All primes in $\mathcal P_S$ have size between $S^{100}$ and $2S^{100}$, and they serve as the alphabet from which independent random primes are drawn in the probabilistic part of the argument. The lower bound $S^{99}$ on their number is what makes a random prime from $\mathcal P_S$ unlikely to divide a fixed integer $u$, and what makes every single value of a product of a few random primes improbable.
--
--   **Formalization Note** The set is `scalePrimes S := dyadicPrimes ⌊S^100⌋₊`, where `dyadicPrimes n` is the finset of primes in `Ioc n (2*n)` and `⌊·⌋₊` is the natural-number floor. The hypothesis $S\ge2$ already follows from $\log S\ge1$ but is stated separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/PrimeLists.lean#L138-L170

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

theorem OAI.ShortEgyptian.scalePrimes_card (S : ℝ) (hS : 2 ≤ S) (hlog : 1 ≤ Real.log S)
    (hbig : 4000*Real.log S ≤ S) : S^99 ≤ ((scalePrimes S).card:ℝ) := by sorry
