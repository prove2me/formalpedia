-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_smul_def
-- name    : GlobalTheory.LatHecke.smul_def
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:13:07.62843+00:00
-- url     : https://prove2.me/theorems/dcef73de-c1aa-40cf-91f2-6a319b13f14e
-- title:
--   Lat Hecke: smul def
-- statement:
--   The Lat Hecke construction uses the smul def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L90-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L90-L90

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

theorem GlobalTheory.LatHecke.smul_def (g : GL (Fin r) K) (L : Lat O K r) : g • L = glLat g L := by sorry
