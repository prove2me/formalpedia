-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_embHom_castSucc_last
-- name    : GlobalTheory.JR.Step.embHom_castSucc_last
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:36:38.345436+00:00
-- url     : https://prove2.me/theorems/ceb98dca-9761-4855-8869-1b574cc4ecca
-- title:
--   Step: emb Hom cast Succ last
-- statement:
--   The Step construction uses the emb Hom cast Succ last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActLiftHermitianBlockMemIntegralUnitaryMu.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActLiftHermitianBlockMemIntegralUnitaryMu.lean#L20-L25

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

theorem GlobalTheory.JR.Step.embHom_castSucc_last (M : Matrix (Fin r) (Fin r) E) (a : Fin r) :
    embHom r E M (Fin.castSucc a) (Fin.last r) = 0 := by sorry
