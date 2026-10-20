-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteAlphabet_finite_tree_alphabet_bounds
-- name    : OAI.TreeEdit.BinaryLower.FiniteAlphabet.finite_tree_alphabet_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:06:58.713282+00:00
-- url     : https://prove2.me/theorems/7347c594-560e-43d8-af28-becefbebf0c1
-- title:
--   The finite-tree alphabet is nonempty and not too large
-- statement:
--   Let $k\ge2$ and $Q$ assign to each leaf $a\in\{1..20k\}^k$ an integer with $0<Q(a)\le2k^{5k}$. Then the tagged alphabet $\Gamma=\{(a,r):\ r\in\mathbb Z/Q(a)\}$ is finite with
--   $$
--   1\le|\Gamma|\le(20k\cdot k^{20k})^k ,
--   $$
--   the source word length.
--
--   So the source words use at most as many letters as their length.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteAlphabet.lean#L80-L99

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

theorem OAI.TreeEdit.BinaryLower.FiniteAlphabet.finite_tree_alphabet_bounds {k : ℕ} (hk : 2 ≤ k)
    (Q : Word (Fin (20 * k)) k → ℕ)
    (hQpos : ∀ a, 0 < Q a) (hQupper : ∀ a, Q a ≤ 2 * k ^ (5 * k)) :
    Finite (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ∧
    1 ≤ Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ∧
    Nat.card (Σ a : Word (Fin (20 * k)) k, ZMod (Q a)) ≤
      (20 * k * k ^ (20 * k)) ^ k := by sorry
