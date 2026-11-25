-- Prove2me | Theorems.Thm_GlobalTheory_FrobRoot_mm_add_pow
-- name    : GlobalTheory.FrobRoot.mm_add_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:29.485299+00:00
-- url     : https://prove2.me/theorems/74eb04a6-4cbf-4972-beed-3dfcf05e9691
-- title:
--   Frob Root: mm add pow
-- statement:
--   The Frob Root construction uses the mm add pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowAdditiveAndRoots.lean#L43-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowAdditiveAndRoots.lean#L43-L54

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodOfMemSlots
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowAdditiveAndRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds GlobalTheory.LeafTerm
open GlobalTheory GlobalTheory.FrobRoot
variable {C : Type} [Field C] {V : VF C}

theorem GlobalTheory.FrobRoot.mm_add_pow (e : ℕ) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.MM ((a + b) ^ (V.l ^ e) - (a ^ (V.l ^ e) + b ^ (V.l ^ e))) := by sorry
