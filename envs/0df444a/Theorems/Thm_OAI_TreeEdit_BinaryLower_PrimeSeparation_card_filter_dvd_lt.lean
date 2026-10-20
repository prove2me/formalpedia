-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_PrimeSeparation_card_filter_dvd_lt
-- name    : OAI.TreeEdit.BinaryLower.PrimeSeparation.card_filter_dvd_lt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:05:50.896691+00:00
-- url     : https://prove2.me/theorems/22734caa-d09b-4da7-933c-b45cc179586b
-- title:
--   Few large primes divide a small positive integer
-- statement:
--   Let $s$ be a finite index set and $p:s\to\mathbb N$ injective with values primes at least $L\ge1$. If $0<n<L^q$, then
--   $$
--   \bigl|\{i\in s:\ p_i\mid n\}\bigr|<q .
--   $$
--
--   A positive integer below $L^q$ has fewer than $q$ distinct prime factors of size at least $L$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/PrimeSeparation.lean#L16-L42

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.PrimeSeparation.card_filter_dvd_lt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℕ) (L q n : ℕ)
    (hp : ∀ i ∈ s, (p i).Prime)
    (hinj : Set.InjOn p (s : Set ι))
    (hL : ∀ i ∈ s, L ≤ p i)
    (hLpos : 0 < L) (hnpos : 0 < n) (hn : n < L ^ q) :
    (s.filter fun i => p i ∣ n).card < q := by sorry
