-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_BaseChange_herm_basis_change
-- name    : GlobalTheory.UnitLemma.BaseChange.herm_basis_change
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:26:51.16197+00:00
-- url     : https://prove2.me/theorems/c8d07a2c-490f-493d-bbc6-fb28415c697e
-- title:
--   Base Change: herm basis change
-- statement:
--   The Base Change construction uses the herm basis change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OrthonormalIffUnitary.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OrthonormalIffUnitary.lean#L25-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ValIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OrthonormalIffUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.BaseChange
variable {K : UQ} (B : InvAlg K)

theorem GlobalTheory.UnitLemma.BaseChange.herm_basis_change (x : B.A) {n : ℕ} (e e' : Module.Basis (Fin n) K.E B.A)
    (he : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (i j : Fin n) :
    B.herm x (e' i) (e' j) = ∑ k, e.toMatrix e' k i * K.c (e.toMatrix e' k j) := by sorry
