-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticEtale_exists_isUnit_sub
-- name    : GlobalTheory.QuadraticEtale.exists_isUnit_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:39.251698+00:00
-- url     : https://prove2.me/theorems/916576bd-f1d3-4413-8878-10adeb80c562
-- title:
--   Quadratic Etale: exists is Unit sub
-- statement:
--   The Quadratic Etale construction uses the exists is Unit sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L325-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L325-L332

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

theorem GlobalTheory.QuadraticEtale.exists_isUnit_sub (hrank : finrank R S = 2) (σ : S ≃ₐ[R] S) (hσ : σ ≠ 1) :
    ∃ ω, IsUnit (ω - σ ω) := by sorry
