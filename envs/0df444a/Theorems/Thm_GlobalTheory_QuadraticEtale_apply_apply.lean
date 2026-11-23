-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticEtale_apply_apply
-- name    : GlobalTheory.QuadraticEtale.apply_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:35.484381+00:00
-- url     : https://prove2.me/theorems/2ad375a2-3221-4978-a740-c4d4dbcba154
-- title:
--   Quadratic Etale: apply apply
-- statement:
--   The Quadratic Etale construction uses the apply apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L318-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L318-L323

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.QuadraticEtale
open Module
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
  [Module.Free R S] [Algebra.FormallyUnramified R S]

theorem GlobalTheory.QuadraticEtale.apply_apply (hrank : finrank R S = 2) (σ : S ≃ₐ[R] S) (hσ : σ ≠ 1) (x : S) :
    σ (σ x) = x := by sorry
