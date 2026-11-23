-- Prove2me | Theorems.Thm_GlobalTheory_LowerOps_inK_mem_eigK
-- name    : GlobalTheory.LowerOps.inK_mem_eigK
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:23.605476+00:00
-- url     : https://prove2.me/theorems/53c644cc-2add-438e-b59e-4ff41755c85d
-- title:
--   Lower Ops: in K mem eig K
-- statement:
--   The Lower Ops construction uses the in K mem eig K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodConjugateIntegral.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodConjugateIntegral.lean#L30-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodConjugateIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.LowerOps
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem GlobalTheory.LowerOps.inK_mem_eigK {ρ : orderC c →+* Module.End O H} {σ : E →+* K} {y : H} (hy : y ∈ eigLat (K := K) ρ σ) :
    inK K H y ∈ eigK ρ σ := by sorry
