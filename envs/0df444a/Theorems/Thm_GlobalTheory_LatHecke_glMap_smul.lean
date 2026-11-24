-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_glMap_smul
-- name    : GlobalTheory.LatHecke.glMap_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:13.94222+00:00
-- url     : https://prove2.me/theorems/a990db56-09e3-4fd0-9273-31a55cac5ec8
-- title:
--   Lat Hecke: gl Map smul
-- statement:
--   The Lat Hecke construction uses the gl Map smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L56-L57

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
omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]

theorem GlobalTheory.LatHecke.glMap_smul (g : GL (Fin r) K) (I : Ideal O) (L : Submodule O (Fin r → K)) :
    glMap g (I • L) = I • glMap g L := by sorry
