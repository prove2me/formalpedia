-- Prove2me | Theorems.Thm_GlobalTheory_TraceIso_split_of_hom
-- name    : GlobalTheory.TraceIso.split_of_hom
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:11:13.946291+00:00
-- url     : https://prove2.me/theorems/d7236afe-8b5a-467c-928b-8d6a2bef328b
-- title:
--   Trace Iso: split of hom
-- statement:
--   The Trace Iso construction uses the split of hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyLinearEquivOfCharpolyEq.lean#L79-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyLinearEquivOfCharpolyEq.lean#L79-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceIso
open Module
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

theorem GlobalTheory.TraceIso.split_of_hom [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (f : V →ₗ[A] W) (hf : f ≠ 0) :
    ∃ (P : Submodule A V) (Q S : Submodule A W), Nonempty (V ≃ₗ[A] P × S) ∧ Nonempty (W ≃ₗ[A] Q × S) ∧
      finrank k P < finrank k V ∧ finrank k Q < finrank k W := by sorry
