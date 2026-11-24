-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_embHom_last_castSucc
-- name    : GlobalTheory.JR.Step.embHom_last_castSucc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:36:43.847126+00:00
-- url     : https://prove2.me/theorems/caeed759-e787-49bd-953e-4e80b22adfd0
-- title:
--   Step: emb Hom last cast Succ
-- statement:
--   The Step construction uses the emb Hom last cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActLiftHermitianBlockMemIntegralUnitaryMu.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActLiftHermitianBlockMemIntegralUnitaryMu.lean#L27-L32

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActLiftHermitianBlockMemIntegralUnitaryMu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
variable {r : ℕ} {E : Type} [Field E]

theorem GlobalTheory.JR.Step.embHom_last_castSucc (M : Matrix (Fin r) (Fin r) E) (b : Fin r) :
    embHom r E M (Fin.last r) (Fin.castSucc b) = 0 := by sorry
