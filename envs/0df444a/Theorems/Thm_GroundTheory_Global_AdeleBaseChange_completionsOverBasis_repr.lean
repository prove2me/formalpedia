-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_completionsOverBasis_repr
-- name    : GroundTheory.Global.AdeleBaseChange.completionsOverBasis_repr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:34:49.997395+00:00
-- url     : https://prove2.me/theorems/68841d29-45c6-5c05-9d0f-7c5cafe73117
-- title:
--   Adele Base Change: completions Over Basis repr
-- statement:
--   The Adele Base Change construction uses the completions Over Basis repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/CompletionsOverBasisRepr.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/CompletionsOverBasisRepr.lean#L43-L45

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
omit [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Global.AdeleBaseChange.completionsOverBasis_repr (v : HeightOneSpectrum (𝓞 K)) (z : CompletionsOver L v)
    (i : ι) : (completionsOverBasis b v).repr z i = localCoord b v i z := by sorry
