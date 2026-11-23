-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_gramDet_eq_norm_mul
-- name    : GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:26.705844+00:00
-- url     : https://prove2.me/theorems/aca6e71c-2e0d-4a66-a8ac-714cab45515f
-- title:
--   Inv Alg: gram Det eq norm mul
-- statement:
--   The Inv Alg construction uses the gram Det eq norm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GramDetEqNormMulGramDetOne.lean#L6-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GramDetEqNormMulGramDetOne.lean#L6-L22

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GramDetEqNormMulGramDetOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.InvAlg

theorem GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul (K : UQ) (B : InvAlg K) (x : B.A) :
    B.gramDet x = Algebra.norm K.E x * B.gramDet 1 := by sorry
