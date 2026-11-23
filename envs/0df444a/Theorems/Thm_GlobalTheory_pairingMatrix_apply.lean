-- Prove2me | Theorems.Thm_GlobalTheory_pairingMatrix_apply
-- name    : GlobalTheory.pairingMatrix_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:54.074635+00:00
-- url     : https://prove2.me/theorems/34f0d346-61e2-44dd-b3ab-67430c89b9a8
-- title:
--   Global Theory: pairing Matrix apply
-- statement:
--   The Global Theory construction uses the pairing Matrix apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L19-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.pairingMatrix_apply (ε : ι → Module.Dual R M) (e' : ι → M) (a' a : ι) :
    pairingMatrix ε e' a' a = ε a (e' a') := by sorry

attribute [defeq] GlobalTheory.pairingMatrix_apply
