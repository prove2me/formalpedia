-- Prove2me | Theorems.Thm_OAI_FiniteCircle_primeInterval_card_cubic
-- name    : OAI.FiniteCircle.primeInterval_card_cubic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:44:01.135984+00:00
-- url     : https://prove2.me/theorems/57dd590a-2060-4461-b522-6b56ab8f8271
-- title:
--   At least $h^2$ primes in $(h^3,2h^3]$ for $h\ge10^6$
-- statement:
--   For every integer $h\ge10^6$ the interval $(h^3,2h^3]$ contains at least $h^2$ primes:
--
--   $$
--   \#\{p\ \text{prime}:\ h^3<p\le2h^3\}\ \ge\ h^2 .
--   $$
--
--   The estimate supplies enough primes to fill an $h\times h$ array of pairwise distinct primes in $(h^3,2h^3]$, which is the prime array (one row of $h$ primes for each of $h$ levels) underlying the circle-word constructions of the edit-distance lower bound.
--
--   **Formalization Note** The set counted is `primeInterval (h^3)`, the finite set of primes in $(h^3,2\cdot h^3]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Primes.lean#L101-L152

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

theorem OAI.FiniteCircle.primeInterval_card_cubic (h : ℕ) (hh : 1000000 ≤ h) :
    h^2 ≤ (primeInterval (h^3)).card := by sorry
