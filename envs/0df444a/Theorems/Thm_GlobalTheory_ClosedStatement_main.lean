-- Prove2me | Theorems.Thm_GlobalTheory_ClosedStatement_main
-- name    : GlobalTheory.ClosedStatement.main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:14:55.658552+00:00
-- url     : https://prove2.me/theorems/cccab58f-84e4-4683-abce-07948362d3f6
-- title:
--   Closed Statement: main
-- statement:
--   The Closed Statement construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImportsTer.lean#L7-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImportsTer.lean#L7-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedStatement
open Ideal Module

theorem GlobalTheory.ClosedStatement.main {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (m : Ideal R)
    [hm : Ideal.IsMaximal m] (hne : Ideal.map f m ≠ ⊤) :
    ∃ (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = (1 : A) ∧
      (∀ x : A, ∃ a : ι →₀ R, (x - Finsupp.sum a fun (i : ι) (y : R) ↦ (f : R → A) y * b i)
        ∈ Ideal.map f m) ∧
      ∀ a : ι →₀ R, (Finsupp.sum a fun (i : ι) (y : R) ↦ (f : R → A) y * b i) ∈ Ideal.map f m →
        ∀ i : ι, (a : ι → R) i ∈ m := by sorry
