-- Prove2me | Theorems.Thm_GlobalTheory_exists_awayFrac_common
-- name    : GlobalTheory.exists_awayFrac_common
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:29.102614+00:00
-- url     : https://prove2.me/theorems/7b5d4358-a62e-449e-af16-6f80ac3beafc
-- title:
--   Global Theory: exists away Frac common
-- statement:
--   The Global Theory construction uses the exists away Frac common property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsBaseChangeAwayOfIntertwine.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsBaseChangeAwayOfIntertwine.lean#L17-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeAwayOfIntertwine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory
variable {R₀ R A₀ A : Type} [CommRing R₀] [CommRing R] [CommRing A₀] [CommRing A] [Algebra R₀ R]
  [Algebra R₀ A₀] [Algebra R A] [Algebra R₀ A] [IsScalarTower R₀ R A]
  {N₀ N : Type} [AddCommGroup N₀] [Module R₀ N₀] [Module A₀ N₀] [IsScalarTower R₀ A₀ N₀]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] [Module R₀ N]
  [IsScalarTower R₀ R N] [IsScalarTower R₀ A N]

theorem GlobalTheory.exists_awayFrac_common {f : A₀} (z w : LocalizedModule.Away f N₀) :
    ∃ k m m', awayFrac N₀ f k m = z ∧ awayFrac N₀ f k m' = w := by sorry
