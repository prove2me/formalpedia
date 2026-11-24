-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_OrthoSelfDual_herm_basis
-- name    : GlobalTheory.UnitLemma.OrthoSelfDual.herm_basis
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:28:55.737652+00:00
-- url     : https://prove2.me/theorems/b9fbfbef-3c21-4b75-a067-ccc67c516ca6
-- title:
--   Ortho Self Dual: herm basis
-- statement:
--   The Ortho Self Dual construction uses the herm basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanSelfDual.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanSelfDual.lean#L19-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpanSelfDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.OrthoSelfDual

theorem GlobalTheory.UnitLemma.OrthoSelfDual.herm_basis {K : UQ} (B : InvAlg K) (x : B.A) (n : ℕ) (e : Module.Basis (Fin n) K.E B.A)
    (h : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (y : B.A) (j : Fin n) :
    B.herm x y (e j) = e.repr y j := by sorry
