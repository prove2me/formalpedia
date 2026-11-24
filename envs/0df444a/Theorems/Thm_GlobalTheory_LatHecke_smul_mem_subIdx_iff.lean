-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_smul_mem_subIdx_iff
-- name    : GlobalTheory.LatHecke.smul_mem_subIdx_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:13:07.37435+00:00
-- url     : https://prove2.me/theorems/3bce18f8-14d5-4cc2-9a5d-38267fa2bcfb
-- title:
--   Lat Hecke: smul mem sub Idx iff
-- statement:
--   The Lat Hecke construction uses the smul mem sub Idx iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L251-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L251-L253

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

theorem GlobalTheory.LatHecke.smul_mem_subIdx_iff (g : GL (Fin r) K) (n : ℕ) (M L : Lat O K r) :
    g • M ∈ subIdx n (g • L) ↔ M ∈ subIdx n L := by sorry
