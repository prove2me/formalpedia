-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_subIdx_zero
-- name    : GlobalTheory.LatHecke.subIdx_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:13:07.180799+00:00
-- url     : https://prove2.me/theorems/cfc57cd2-b8d3-420f-b545-2bb2c97546d4
-- title:
--   Lat Hecke: sub Idx zero
-- statement:
--   The Lat Hecke construction uses the sub Idx zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L183-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L183-L189

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

theorem GlobalTheory.LatHecke.subIdx_zero (L : Lat O K r) : subIdx 0 L = {L} := by sorry
