-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_dvd_of_idem
-- name    : GlobalTheory.HeckeTate.dvd_of_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:24.522144+00:00
-- url     : https://prove2.me/theorems/f067b324-94bf-4871-951b-62aed027b343
-- title:
--   Hecke Tate: dvd of idem
-- statement:
--   The Hecke Tate construction uses the dvd of idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L9-L19

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

theorem GlobalTheory.HeckeTate.dvd_of_idem {N x : R} (h : N ∣ x * (1 - x))
    (hx : ∀ q : Ideal R, q.IsMaximal → N ∈ q → x ∈ q) : N ∣ x := by sorry
