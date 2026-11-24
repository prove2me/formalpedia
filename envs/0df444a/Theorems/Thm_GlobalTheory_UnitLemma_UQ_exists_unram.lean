-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UQ_exists_unram
-- name    : GlobalTheory.UnitLemma.UQ.exists_unram
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:34:20.063803+00:00
-- url     : https://prove2.me/theorems/6ebe9dc6-0cc1-4c2f-86cc-ca12a4d00364
-- title:
--   UQ: exists unram
-- statement:
--   The UQ construction uses the exists unram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean#L239-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean#L239-L286

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
open Bridge

theorem GlobalTheory.UnitLemma.UQ.exists_unram : ∀ K : UQ, ∃ (F : Type) (_ : NontriviallyNormedField F) (nE : NontriviallyNormedField K.E) (hE : nE.toField = K.fE) (_ : @NormedAlgebra F K.E _ nE.toNormedField.toNormedCommRing.toSeminormedCommRing.toSeminormedRing) (st : @StarRing K.E nE.toNormedField.toNormedCommRing.toRing.toNonAssocRing.toNonUnitalNonAssocRing.toNonUnitalNonAssocSemiring), @GlobalTheory.JR.Unram F K.E _ nE _ st ∧ (∀ y, st.star y = K.c y) ∧ ∀ y : K.E, nE.norm y ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range := by sorry
