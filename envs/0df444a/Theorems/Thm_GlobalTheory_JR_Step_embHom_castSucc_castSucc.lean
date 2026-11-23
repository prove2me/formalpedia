-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_embHom_castSucc_castSucc
-- name    : GlobalTheory.JR.Step.embHom_castSucc_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:51.138959+00:00
-- url     : https://prove2.me/theorems/03947c8c-b12e-406a-a6e0-30888a3d4098
-- title:
--   Step: emb Hom cast Succ cast Succ
-- statement:
--   The Step construction uses the emb Hom cast Succ cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActLiftHermitianBlockMemIntegralUnitaryMu.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActLiftHermitianBlockMemIntegralUnitaryMu.lean#L12-L18

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

theorem GlobalTheory.JR.Step.embHom_castSucc_castSucc (M : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    embHom r E M (Fin.castSucc a) (Fin.castSucc b) = M a b := by sorry
