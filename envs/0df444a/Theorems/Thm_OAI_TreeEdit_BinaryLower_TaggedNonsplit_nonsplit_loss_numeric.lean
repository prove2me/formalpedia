-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedNonsplit_nonsplit_loss_numeric
-- name    : OAI.TreeEdit.BinaryLower.TaggedNonsplit.nonsplit_loss_numeric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:15:17.613083+00:00
-- url     : https://prove2.me/theorems/01d9c3d9-e17c-4898-a734-3f830c0c412b
-- title:
--   Nonsplit rows bound the number of matches
-- statement:
--   Words of length $TmB$ are read as $T$ rows of $m$ blocks of width $B$: position $t$ lies in block $\lfloor t/B\rfloor$, with tag $\lfloor t/B\rfloor\bmod m$ and row $\lfloor\lfloor t/B\rfloor/m\rfloor$. Let $u$ be an injective sequence of $N$ positions below $TmB$, with $m,B>0$, $S\subseteq\{0..T-1\}$ and $d\in\mathbb R$. Suppose every row $r\notin S$ contains at most $mB-d$ of the positions. Then
--   $$
--   d\,(T-|S|)\le TmB-N .
--   $$
--
--   This is the loss count for nonsplit rows with capacity $mB$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedNonsplit.lean#L220-L256

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TaggedNonsplit
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.TaggedNonsplit.nonsplit_loss_numeric {N T m B : ℕ}
    (u : Fin N → ℕ) (hu : Function.Injective u)
    (hm : 0 < m) (hB : 0 < B) (hub : ∀ i, u i < T * m * B)
    (S : Finset ℕ) (hS : S ⊆ Finset.range T) (d : ℝ)
    (hnonsplit : ∀ r < T, r ∉ S →
      ((Finset.univ.filter fun i => u i / B / m = r).card : ℝ) ≤
        (m * B : ℕ) - d) :
    d * ((T : ℝ) - S.card) ≤ ((T * m * B - N : ℕ) : ℝ) := by sorry
