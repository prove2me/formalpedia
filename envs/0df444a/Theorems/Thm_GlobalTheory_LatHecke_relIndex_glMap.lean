-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_relIndex_glMap
-- name    : GlobalTheory.LatHecke.relIndex_glMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:29.916313+00:00
-- url     : https://prove2.me/theorems/a6305c4f-6a2c-4edf-ad32-eaa2a35ec0b1
-- title:
--   Lat Hecke: rel Index gl Map
-- statement:
--   The Lat Hecke construction uses the rel Index gl Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L61-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean#L61-L69

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

theorem GlobalTheory.LatHecke.relIndex_glMap (g : GL (Fin r) K) (M L : Submodule O (Fin r → K)) :
    (glMap g M).toAddSubgroup.relIndex (glMap g L).toAddSubgroup =
      M.toAddSubgroup.relIndex L.toAddSubgroup := by sorry
