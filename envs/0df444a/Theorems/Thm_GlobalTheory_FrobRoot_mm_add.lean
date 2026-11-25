-- Prove2me | Theorems.Thm_GlobalTheory_FrobRoot_mm_add
-- name    : GlobalTheory.FrobRoot.mm_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:45.114324+00:00
-- url     : https://prove2.me/theorems/6fb76634-a0af-4dca-b2ce-b96358dd1b11
-- title:
--   Frob Root: mm add
-- statement:
--   The Frob Root construction uses the mm add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowAdditiveAndRoots.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowAdditiveAndRoots.lean#L21-L22

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

theorem GlobalTheory.FrobRoot.mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by sorry
