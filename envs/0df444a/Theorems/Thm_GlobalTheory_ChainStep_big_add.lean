-- Prove2me | Theorems.Thm_GlobalTheory_ChainStep_big_add
-- name    : GlobalTheory.ChainStep.big_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:32:44.556177+00:00
-- url     : https://prove2.me/theorems/fd9f7dcc-87de-40b4-bdfd-fb1f21d0906f
-- title:
--   Chain Step: big add
-- statement:
--   The Chain Step construction uses the big add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainStepKernelRankLeModMaxIdeal.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainStepKernelRankLeModMaxIdeal.lean#L84-L91

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainStepKernelRankLeModMaxIdeal
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
open GlobalTheory GlobalTheory.ChainStep
variable {C : Type} [Field C] {V : VF C}

theorem GlobalTheory.ChainStep.big_add {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (h : X.big g a) (s : ℕ) :
    X.big g (a + ((2 * s : ℕ) : ZMod d)) := by sorry
