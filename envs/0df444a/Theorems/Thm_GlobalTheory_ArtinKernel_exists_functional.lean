-- Prove2me | Theorems.Thm_GlobalTheory_ArtinKernel_exists_functional
-- name    : GlobalTheory.ArtinKernel.exists_functional
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:58:45.585978+00:00
-- url     : https://prove2.me/theorems/b72d9a8a-536a-49f1-a541-604ca803371b
-- title:
--   Artin Kernel: exists functional
-- statement:
--   The Artin Kernel construction uses the exists functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearOfMulPeriod.lean#L119-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearOfMulPeriod.lean#L119-L154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.ArtinKernel
variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]

theorem GlobalTheory.ArtinKernel.exists_functional {ι : Type*} (δ : ι → R) (hδ : ∃ i, δ i ≠ 0) :
    ∃ lam : R →ₗ[ℂ] ℂ, (∃ i, lam (δ i) ≠ 0) ∧
      ∀ i, ∀ r ∈ IsLocalRing.maximalIdeal R, lam (r * δ i) = 0 := by sorry
