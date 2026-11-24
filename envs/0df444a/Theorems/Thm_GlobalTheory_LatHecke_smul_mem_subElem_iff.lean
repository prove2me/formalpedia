-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_smul_mem_subElem_iff
-- name    : GlobalTheory.LatHecke.smul_mem_subElem_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:13.967341+00:00
-- url     : https://prove2.me/theorems/a6871ce0-f791-4cda-813e-d92c4e3f0abc
-- title:
--   Lat Hecke: smul mem sub Elem iff
-- statement:
--   The Lat Hecke construction uses the smul mem sub Elem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L255-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L255-L259

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

theorem GlobalTheory.LatHecke.smul_mem_subElem_iff (g : GL (Fin r) K) (k : ℕ) (M L : Lat O K r) :
    g • M ∈ subElem k (g • L) ↔ M ∈ subElem k L := by sorry
