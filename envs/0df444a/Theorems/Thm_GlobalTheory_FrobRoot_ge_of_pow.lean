-- Prove2me | Theorems.Thm_GlobalTheory_FrobRoot_ge_of_pow
-- name    : GlobalTheory.FrobRoot.ge_of_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:27.453551+00:00
-- url     : https://prove2.me/theorems/024acd21-1d4c-4459-b13e-d11c827088e4
-- title:
--   Frob Root: ge of pow
-- statement:
--   The Frob Root construction uses the ge of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowAdditiveAndRoots.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowAdditiveAndRoots.lean#L36-L41

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

theorem GlobalTheory.FrobRoot.ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (ha : V.Ge 0 (a ^ n)) : V.Ge 0 a := by sorry
