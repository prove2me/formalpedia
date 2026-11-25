-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_heckeAll_smul
-- name    : GlobalTheory.LatHecke.heckeAll_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:12:49.445609+00:00
-- url     : https://prove2.me/theorems/a779b04f-aed0-4f43-a378-2877e6102398
-- title:
--   Lat Hecke: hecke All smul
-- statement:
--   The Lat Hecke construction uses the hecke All smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L288-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L288-L293

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

theorem GlobalTheory.LatHecke.heckeAll_smul (g : GL (Fin r) K) (n : ℕ) (φ : Lat O K r → E) (L : Lat O K r) :
    heckeAll n φ (g • L) = heckeAll n (fun M => φ (g • M)) L := by sorry
