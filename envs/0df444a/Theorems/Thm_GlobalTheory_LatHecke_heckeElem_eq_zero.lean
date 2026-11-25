-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_heckeElem_eq_zero
-- name    : GlobalTheory.LatHecke.heckeElem_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:12:58.388803+00:00
-- url     : https://prove2.me/theorems/c4c5002d-c5e0-49e1-99a4-14015ea4dbba
-- title:
--   Lat Hecke: hecke Elem eq zero
-- statement:
--   The Lat Hecke construction uses the hecke Elem eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L284-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L284-L286

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

theorem GlobalTheory.LatHecke.heckeElem_eq_zero {k : ℕ} (hk : r < k) (φ : Lat O K r → E) (L : Lat O K r) :
    heckeElem k φ L = 0 := by sorry
