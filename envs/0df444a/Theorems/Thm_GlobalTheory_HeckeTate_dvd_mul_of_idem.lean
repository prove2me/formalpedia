-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_dvd_mul_of_idem
-- name    : GlobalTheory.HeckeTate.dvd_mul_of_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:28.694838+00:00
-- url     : https://prove2.me/theorems/62a4d8b6-0e6c-448f-b18a-c4b2ac827ec6
-- title:
--   Hecke Tate: dvd mul of idem
-- statement:
--   The Hecke Tate construction uses the dvd mul of idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L21-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R]

theorem GlobalTheory.HeckeTate.dvd_mul_of_idem {N f g : R} (hf : N ∣ f * (1 - f)) (hg : N ∣ g * (1 - g))
    (h : ∀ q : Ideal R, q.IsMaximal → N ∈ q → f ∈ q ∨ g ∈ q) : N ∣ f * g := by sorry
