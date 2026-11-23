-- Prove2me | Theorems.Thm_GlobalTheory_HullClasses_mulLat_mul
-- name    : GlobalTheory.HullClasses.mulLat_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:32.644978+00:00
-- url     : https://prove2.me/theorems/5906730a-b33a-4701-b1fe-44a4e2c955d9
-- title:
--   Hull Classes: mul Lat mul
-- statement:
--   The Hull Classes construction uses the mul Lat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L18-L23

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

theorem GlobalTheory.HullClasses.mulLat_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (s t : A) (L : Submodule O A) :
    mulLat O (s * t) L = mulLat O s (mulLat O t L) := by sorry
