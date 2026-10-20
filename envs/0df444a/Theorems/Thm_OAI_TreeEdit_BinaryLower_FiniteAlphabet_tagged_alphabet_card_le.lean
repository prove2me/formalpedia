-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteAlphabet_tagged_alphabet_card_le
-- name    : OAI.TreeEdit.BinaryLower.FiniteAlphabet.tagged_alphabet_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:06:06.692707+00:00
-- url     : https://prove2.me/theorems/ffdc7d73-e77b-4a37-83f5-4611c4dbd4bb
-- title:
--   Size of a tagged cyclic alphabet
-- statement:
--   Let $Q$ assign to each word $a$ of length $k$ over $\{1..m\}$ an integer with $0<Q(a)\le H$. Then the tagged alphabet $\{(a,r):\ r\in\mathbb Z/Q(a)\}$ satisfies
--   $$
--   \bigl|\{(a,r)\}\bigr|=\sum_aQ(a)\le m^k\,H .
--   $$
--
--   Each of the $m^k$ tags carries at most $H$ residues.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteAlphabet.lean#L58-L78

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
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.FiniteAlphabet.tagged_alphabet_card_le {m k H : ℕ}
    (Q : Word (Fin m) k → ℕ)
    (hQpos : ∀ a, 0 < Q a) (hQupper : ∀ a, Q a ≤ H) :
    Nat.card (Σ a : Word (Fin m) k, ZMod (Q a)) ≤ m ^ k * H := by sorry
