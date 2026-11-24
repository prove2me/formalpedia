-- Prove2me | Theorems.Thm_GlobalTheory_StepData_lam_iter_principal
-- name    : GlobalTheory.StepData.lam_iter_principal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:41.639692+00:00
-- url     : https://prove2.me/theorems/e91825c9-3c0e-4fb8-aeb0-530c27565e40
-- title:
--   Step Data: lam iter principal
-- statement:
--   The Step Data construction uses the lam iter principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IterPrincipalSpec.lean#L115-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IterPrincipalSpec.lean#L115-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IterPrincipalSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.StepData ValuativeRel Matrix
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

theorem GlobalTheory.StepData.lam_iter_principal (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ)
    (g : ((TypeDatum.principal k r).iter t μ hμ j).J) (d : Fin j → kˣ)
    (hd : ∀ c, (d c : k) = (Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val c).det) :
    ((TypeDatum.principal k r).iter t μ hμ j).lam g = ∏ c : Fin j, μ (c.val + 1) (d c) := by sorry
