-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_toW_same
-- name    : GlobalTheory.MainTerm.toW_same
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:13.410101+00:00
-- url     : https://prove2.me/theorems/4611da3d-0d3a-49ef-b94a-d8450cb61979
-- title:
--   Main Term: to W same
-- statement:
--   The Main Term construction uses the to W same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/HPullWUpGTwoGroupEmbeddingEqRename.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/HPullWUpGTwoGroupEmbeddingEqRename.lean#L12-L14

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HPullWUpGTwoGroupEmbeddingEqRename
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.MainTerm

theorem GlobalTheory.MainTerm.toW_same {C : Type} [Field C] {I : Fin 2 → Type} (g : Fin 2) (u : I g → C) (x : I g) :
    toW g u ⟨g, x⟩ = u x := by sorry
