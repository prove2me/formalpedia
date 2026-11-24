-- Prove2me | Theorems.Thm_GlobalTheory_StepData_TypeDatum_ofResidue_lam
-- name    : GlobalTheory.StepData.TypeDatum.ofResidue_lam
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:48:12.082027+00:00
-- url     : https://prove2.me/theorems/45d4822b-a169-4c52-9bc4-d8b99fbb3f1b
-- title:
--   Type Datum: of Residue lam
-- statement:
--   The Type Datum construction uses the of Residue lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L141-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L141-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
open GlobalTheory.StepData.TypeDatum

theorem GlobalTheory.StepData.TypeDatum.ofResidue_lam (H : Subgroup (GL a 𝓀[k])) (χ : H →* ℂˣ) (u : GL a 𝒪[k])
    (hu : Matrix.GeneralLinearGroup.map (n := a) (IsLocalRing.residue 𝒪[k]) u ∈ H) :
    (ofResidue H χ).lam ⟨Matrix.GeneralLinearGroup.map (n := a) (algebraMap 𝒪[k] k) u, u, hu, rfl⟩ = χ ⟨_, hu⟩ := by sorry
