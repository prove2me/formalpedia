-- Prove2me | Theorems.Thm_GlobalTheory_HullClasses_mem_Lam_iff
-- name    : GlobalTheory.HullClasses.mem_Lam_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:20.598645+00:00
-- url     : https://prove2.me/theorems/3e7af179-61f7-48d2-8f31-4a7619bdb303
-- title:
--   Hull Classes: mem Lam iff
-- statement:
--   The Hull Classes construction uses the mem Lam iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntUnitOfMulLat.lean#L36-L37

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

theorem GlobalTheory.HullClasses.mem_Lam_iff (y : B.A) : y ∈ abelian₂ B ↔ IsIntegral K.O y := by sorry
