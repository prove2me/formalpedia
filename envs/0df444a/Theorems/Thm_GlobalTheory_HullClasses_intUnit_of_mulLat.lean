-- Prove2me | Theorems.Thm_GlobalTheory_HullClasses_intUnit_of_mulLat
-- name    : GlobalTheory.HullClasses.intUnit_of_mulLat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:12:32.4616+00:00
-- url     : https://prove2.me/theorems/ea721200-db09-424c-a4fb-62dd15a8da72
-- title:
--   Hull Classes: int Unit of mul Lat
-- statement:
--   The Hull Classes construction uses the int Unit of mul Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L51-L60

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

theorem GlobalTheory.HullClasses.intUnit_of_mulLat (v : B.Aˣ) (h : mulLat K.O (v : B.A) (abelian₂ B) = abelian₂ B) : v ∈ intUnits K.O B.A := by sorry
