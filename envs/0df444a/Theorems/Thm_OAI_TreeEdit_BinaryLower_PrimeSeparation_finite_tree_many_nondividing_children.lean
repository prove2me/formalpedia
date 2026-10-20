-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_PrimeSeparation_finite_tree_many_nondividing_children
-- name    : OAI.TreeEdit.BinaryLower.PrimeSeparation.finite_tree_many_nondividing_children
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:06:34.828984+00:00
-- url     : https://prove2.me/theorems/7c99bcb6-c70c-4ca2-a85c-6d54806b0546
-- title:
--   Many children have periods not dividing a shifted coefficient
-- statement:
--   Let $k\ge2$, $Q\in\mathbb N$, and let $p_1,\dots,p_{20k}$ be distinct primes with $p_i\ge k^4$, and $R=\prod_jp_j$. Let $z,t\in\mathbb Z$ with $z\ne0$ and $|z|<k^{20k}$. Then
--   $$
--   \bigl|\{i:\ Qp_i\nmid z+tR\}\bigr|\ge10k .
--   $$
--
--   At least half of the $20k$ children see a nonzero shift.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/PrimeSeparation.lean#L73-L109

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

theorem OAI.TreeEdit.BinaryLower.PrimeSeparation.finite_tree_many_nondividing_children
    (k Q : ℕ) (p : Fin (20 * k) → ℕ) (z t : ℤ)
    (hk : 2 ≤ k) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hlarge : ∀ i, k ^ 4 ≤ p i)
    (hz : z ≠ 0) (hsmall : z.natAbs < k ^ (20 * k)) :
    10 * k ≤ (Finset.univ.filter fun i =>
      ¬ ((Q * p i : ℕ) : ℤ) ∣ z + t * (∏ j, p j : ℕ)).card := by sorry
