-- Prove2me | Theorems.Thm_OAI_FiniteCircle_centralBinom_le_interval
-- name    : OAI.FiniteCircle.centralBinom_le_interval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:43:28.358256+00:00
-- url     : https://prove2.me/theorems/95efd59c-ddc3-4a52-8a4f-a00e3698c78a
-- title:
--   Central binomial coefficient bounded by small primes and the primes in $(n,2n]$
-- statement:
--   For every integer $n>2$,
--
--   $$
--   \binom{2n}{n}\le(2n)^{\lfloor\sqrt{2n}\rfloor}\cdot4^{\lfloor 2n/3\rfloor}\cdot\prod_{\substack{p\ \text{prime}\\ n<p\le2n}}p ,
--   $$
--
--   where $\lfloor\sqrt{2n}\rfloor$ is the integer square root of $2n$ and $\lfloor2n/3\rfloor$ is the integer quotient.
--
--   This is the key upper estimate in Erdős's classical proof of Bertrand's postulate: the primes up to $2n/3$ contribute comparatively little to $\binom{2n}{n}$, so most of its size must come from the primes in $(n,2n]$. Together with the lower bound $4^n<n\binom{2n}{n}$ it gives lower bounds for the number of primes in $(n,2n]$; in this development it is used to show that $(h^3,2h^3]$ contains at least $h^2$ primes.
--
--   **Formalization Note** $\binom{2n}{n}$ is `Nat.centralBinom n`, $\lfloor\sqrt{2n}\rfloor$ is `Nat.sqrt (2*n)`, and the product runs over `primeInterval n`, the finite set of primes $p$ with $n<p\le2n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Primes.lean#L11-L78

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.centralBinom_le_interval (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^Nat.sqrt (2*n) * 4^(2*n/3) * ∏ p ∈ primeInterval n, p := by sorry
