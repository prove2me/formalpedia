-- Prove2me | Theorems.Thm_GlobalTheory_HullClasses_mulLat_le_mul
-- name    : GlobalTheory.HullClasses.mulLat_le_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:37:34.424622+00:00
-- url     : https://prove2.me/theorems/40bc0b9a-4519-4db1-bf74-d7449f89bfb5
-- title:
--   Hull Classes: mul Lat le mul
-- statement:
--   The Hull Classes construction uses the mul Lat le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L29-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.HullClasses
variable {K : UQ} (B : InvAlg K)

theorem GlobalTheory.HullClasses.mulLat_le_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (r s t : A) (L : Submodule O A)
    (h : mulLat O s L ≤ mulLat O t L) : mulLat O (r * s) L ≤ mulLat O (r * t) L := by sorry
