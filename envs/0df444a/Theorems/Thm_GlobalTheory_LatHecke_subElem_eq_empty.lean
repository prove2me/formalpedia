-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_subElem_eq_empty
-- name    : GlobalTheory.LatHecke.subElem_eq_empty
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:13.922804+00:00
-- url     : https://prove2.me/theorems/88975857-d79a-4be1-b4bb-027627687731
-- title:
--   Lat Hecke: sub Elem eq empty
-- statement:
--   The Lat Hecke construction uses the sub Elem eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L232-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L232-L242

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

theorem GlobalTheory.LatHecke.subElem_eq_empty {k : ℕ} (hk : r < k)
    (L : Lat O K r) : subElem k L = ∅ := by sorry
