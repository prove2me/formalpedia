-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_PrimeSeparation_finite_tree_row_pair_nondivisibility
-- name    : OAI.TreeEdit.BinaryLower.PrimeSeparation.finite_tree_row_pair_nondivisibility
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:07:05.752377+00:00
-- url     : https://prove2.me/theorems/c4b34058-7a7d-4898-a698-1a18e6dd7fa2
-- title:
--   Row pairs are separated by many child periods
-- statement:
--   Let $k\ge2$, distinct primes $p_1,\dots,p_{20k}\ge k^4$ with product $R$, $Q\in\mathbb N$ coprime to $R$, rows $a,b<k^{20k}$ and $t\in\mathbb Z$ with $Q\nmid t$. Then
--   $$
--   \bigl|\{i:\ Qp_i\nmid(b-a)+tR\}\bigr|\ge10k .
--   $$
--
--   Comparing two rows with a shift not divisible by the parent period, half of the children see a mismatch.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/PrimeSeparation.lean#L123-L147

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

theorem OAI.TreeEdit.BinaryLower.PrimeSeparation.finite_tree_row_pair_nondivisibility
    (k Q : ℕ) (p : Fin (20 * k) → ℕ) (a b : ℕ) (t : ℤ)
    (hk : 2 ≤ k) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hlarge : ∀ i, k ^ 4 ≤ p i)
    (ha : a < k ^ (20 * k)) (hb : b < k ^ (20 * k))
    (hcop : Nat.Coprime Q (∏ j, p j)) (ht : ¬ (Q : ℤ) ∣ t) :
    10 * k ≤ (Finset.univ.filter fun i =>
      ¬ ((Q * p i : ℕ) : ℤ) ∣
        (b : ℤ) - a + t * (∏ j, p j : ℕ)).card := by sorry
