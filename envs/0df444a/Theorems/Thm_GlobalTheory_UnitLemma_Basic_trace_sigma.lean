-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Basic_trace_sigma
-- name    : GlobalTheory.UnitLemma.Basic.trace_sigma
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:36:44.745799+00:00
-- url     : https://prove2.me/theorems/41f0781f-cf8e-4677-a605-fd4ee301914c
-- title:
--   Basic: trace sigma
-- statement:
--   The Basic construction uses the trace sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ValIrreducible.lean#L16-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ValIrreducible.lean#L16-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NLineOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ValIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Basic
variable {K : UQ} (B : InvAlg K)
variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K)

theorem GlobalTheory.UnitLemma.Basic.trace_sigma (u : B.A) :
    Algebra.trace K.E B.A (B.σ u) = K.c (Algebra.trace K.E B.A u) := by sorry
