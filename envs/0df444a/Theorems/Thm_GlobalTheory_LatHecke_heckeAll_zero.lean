-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_heckeAll_zero
-- name    : GlobalTheory.LatHecke.heckeAll_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:09.73324+00:00
-- url     : https://prove2.me/theorems/af1dae5f-230b-4336-bcb6-c35d842ee15e
-- title:
--   Lat Hecke: hecke All zero
-- statement:
--   The Lat Hecke construction uses the hecke All zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L275-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L275-L276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatHecke
open scoped TensorProduct
variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
variable [IsFractionRing O K] (r : ℕ)
variable {O K r}
variable [Finite (IsLocalRing.ResidueField O)]
variable {E : Type} [AddCommMonoid E]

theorem GlobalTheory.LatHecke.heckeAll_zero (φ : Lat O K r → E) : heckeAll 0 φ = φ := by sorry
