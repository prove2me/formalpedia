-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_subElem_zero
-- name    : GlobalTheory.LatHecke.subElem_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:05.701939+00:00
-- url     : https://prove2.me/theorems/ecd13645-792f-45f7-ba3c-72b3df7e6815
-- title:
--   Lat Hecke: sub Elem zero
-- statement:
--   The Lat Hecke construction uses the sub Elem zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L191-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L191-L196

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

theorem GlobalTheory.LatHecke.subElem_zero (L : Lat O K r) : subElem 0 L = {L} := by sorry
