-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_glMap_le_glMap_iff
-- name    : GlobalTheory.LatHecke.glMap_le_glMap_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:13:08.417024+00:00
-- url     : https://prove2.me/theorems/49e150ce-8146-4b30-9a76-bd0a918018cf
-- title:
--   Lat Hecke: gl Map le gl Map iff
-- statement:
--   The Lat Hecke construction uses the gl Map le gl Map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L48-L52

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

theorem GlobalTheory.LatHecke.glMap_le_glMap_iff (g : GL (Fin r) K) (M L : Submodule O (Fin r → K)) :
    glMap g M ≤ glMap g L ↔ M ≤ L := by sorry
