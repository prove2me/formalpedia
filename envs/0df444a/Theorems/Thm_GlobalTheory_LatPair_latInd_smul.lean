-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_latInd_smul
-- name    : GlobalTheory.LatPair.latInd_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:58:36.260393+00:00
-- url     : https://prove2.me/theorems/84b88b92-6ef2-4e48-9f3d-c622981e5621
-- title:
--   Lat Pair: lat Ind smul
-- statement:
--   The Lat Pair construction uses the lat Ind smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L374-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L374-L382

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable [Fintype n']
variable {P : Pair k n'} {Q : Pair k n} {x : Matrix n n' k}
variable [DecidableEq n'] [Fintype n] [DecidableEq n]

theorem GlobalTheory.LatPair.latInd_smul (g : GL n' k) (h : GL n k) (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) :
    latInd (g • S) (h • L) x = latInd S L ((h⁻¹ : GL n k).val * x * g.val) := by sorry
