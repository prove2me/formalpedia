-- Prove2me | Theorems.Thm_GlobalTheory_SepPoint_aeval_mem_adjoin_insert
-- name    : GlobalTheory.SepPoint.aeval_mem_adjoin_insert
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:53:10.114264+00:00
-- url     : https://prove2.me/theorems/5736c318-d5ae-4198-8274-8d6fdf7c2a0c
-- title:
--   Sep Point: aeval mem adjoin insert
-- statement:
--   The Sep Point construction uses the aeval mem adjoin insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveElementSeparabilityCertificate.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimitiveElementSeparabilityCertificate.lean#L20-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin
open GlobalTheory GlobalTheory.SepPoint

theorem GlobalTheory.SepPoint.aeval_mem_adjoin_insert {k F : Type} [Field k] [Field F] [Algebra k F]
    (R : Subalgebra k F) (θ : F) (g : R[X]) :
    aeval θ g ∈ Algebra.adjoin k (insert θ (R : Set F)) := by sorry
