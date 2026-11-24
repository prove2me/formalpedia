-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_exists_basis_pow_of_separable
-- name    : GlobalTheory.UnitLemma.exists_basis_pow_of_separable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:21.482804+00:00
-- url     : https://prove2.me/theorems/d69de45d-3fd7-4994-973f-6a920b82e069
-- title:
--   Unit Lemma: exists basis pow of separable
-- statement:
--   The Unit Lemma construction uses the exists basis pow of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPowerBasisOfCharpolySeparable.lean#L47-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPowerBasisOfCharpolySeparable.lean#L47-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
open Matrix MeasureTheory
open Polynomial

theorem GlobalTheory.UnitLemma.exists_basis_pow_of_separable : ∀ (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K), B.P.Separable →
    ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E
      B.A, ∀ i, e i = B.g ^ (i : ℕ) := by sorry
