-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_StabIndex_smul_eq_mulLat
-- name    : GlobalTheory.UnitLemma.StabIndex.smul_eq_mulLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:29.553825+00:00
-- url     : https://prove2.me/theorems/9f5c94ff-6905-4f80-95de-a104f3d57f1a
-- title:
--   Stab Index: smul eq mul Lat
-- statement:
--   The Stab Index construction uses the smul eq mul Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RelIndexNeZeroOfBetween.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RelIndexNeZeroOfBetween.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelIndexNeZeroOfBetween
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open scoped Pointwise
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.StabIndex
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

theorem GlobalTheory.UnitLemma.StabIndex.smul_eq_mulLat (t : Aˣ) (L : Submodule O A) : t • L = mulLat O (t : A) L := by sorry
