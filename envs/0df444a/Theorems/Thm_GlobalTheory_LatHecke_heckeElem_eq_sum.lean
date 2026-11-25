-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_heckeElem_eq_sum
-- name    : GlobalTheory.LatHecke.heckeElem_eq_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:12:59.967248+00:00
-- url     : https://prove2.me/theorems/2ea9d314-220a-49f0-9a8b-24e566de185a
-- title:
--   Lat Hecke: hecke Elem eq sum
-- statement:
--   The Lat Hecke construction uses the hecke Elem eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L271-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L271-L273

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

theorem GlobalTheory.LatHecke.heckeElem_eq_sum (k : ℕ) (φ : Lat O K r → E) (L : Lat O K r) :
    heckeElem k φ L = ∑ M ∈ (subElem_finite k L).toFinset, φ M := by sorry
