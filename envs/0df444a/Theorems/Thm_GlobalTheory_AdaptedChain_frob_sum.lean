-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedChain_frob_sum
-- name    : GlobalTheory.AdaptedChain.frob_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:33.92636+00:00
-- url     : https://prove2.me/theorems/8dcfb792-f838-4778-a455-f48acbd883a8
-- title:
--   Adapted Chain: frob sum
-- statement:
--   The Adapted Chain construction uses the frob sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L25-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L25-L39

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

theorem GlobalTheory.AdaptedChain.frob_sum {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i, V.Ge 0 (f i)) (k : ℕ) :
    V.Ge 1 ((∑ i ∈ s, f i) ^ (V.l ^ k) - ∑ i ∈ s, f i ^ (V.l ^ k)) := by sorry
