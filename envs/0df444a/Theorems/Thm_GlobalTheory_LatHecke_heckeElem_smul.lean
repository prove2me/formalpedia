-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_heckeElem_smul
-- name    : GlobalTheory.LatHecke.heckeElem_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:12:52.249694+00:00
-- url     : https://prove2.me/theorems/9fc3e97e-a817-4060-bed0-a21ef47a5ce7
-- title:
--   Lat Hecke: hecke Elem smul
-- statement:
--   The Lat Hecke construction uses the hecke Elem smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L295-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L295-L300

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

theorem GlobalTheory.LatHecke.heckeElem_smul (g : GL (Fin r) K) (k : ℕ) (φ : Lat O K r → E) (L : Lat O K r) :
    heckeElem k φ (g • L) = heckeElem k (fun M => φ (g • M)) L := by sorry
