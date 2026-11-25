-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_BaseChange_orthonormal_iff_unitary
-- name    : GlobalTheory.UnitLemma.BaseChange.orthonormal_iff_unitary
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:31.713796+00:00
-- url     : https://prove2.me/theorems/aee8f586-2149-5855-a5bd-d1e02e82f59a
-- title:
--   Base Change: orthonormal iff unitary
-- statement:
--   The Base Change construction uses the orthonormal iff unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OrthonormalIffUnitary.lean#L34-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OrthonormalIffUnitary.lean#L34-L54

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

theorem GlobalTheory.UnitLemma.BaseChange.orthonormal_iff_unitary : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (n : ℕ) (e e' : Module.Basis (Fin n) K.E B.A),
    (∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) →
    ((∀ i j, B.herm x (e' i) (e' j) = if i = j then 1 else 0) ↔ ((e.toMatrix e').map K.c)ᵀ * e.toMatrix e' = 1) := by sorry
