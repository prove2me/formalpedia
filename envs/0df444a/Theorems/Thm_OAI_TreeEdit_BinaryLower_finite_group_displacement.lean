-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_finite_group_displacement
-- name    : OAI.TreeEdit.BinaryLower.finite_group_displacement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:45:24.373684+00:00
-- url     : https://prove2.me/theorems/40c21d67-06bd-4b0b-8ea2-d3fd0db17039
-- title:
--   Spectral formula for translation displacements of l1 maps
-- statement:
--   Let $A$ be a finite abelian group and $F:A\to\ell_1$. Then there is $H\ge0$ on the characters of $A$ such that for every $z\in A$,
--   $$
--   \mathbb E_x\|F(x+z)-F(x)\|_1=\sum_\chi|1-\chi(z)|^2H(\chi).
--   $$
--
--   The average displacement under translation is a positive combination of the multipliers $|1-\chi(z)|^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteDisplacement.lean#L74-L95

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.finite_group_displacement {A : Type*} [AddCommGroup A] [Fintype A]
    (F : A → RealL1) :
    ∃ H : AddChar A ℂ → ℝ, (∀ χ, 0 ≤ H χ) ∧
      ∀ z, (𝔼 x, ‖F (x + z) - F x‖) =
        ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * H χ := by sorry
