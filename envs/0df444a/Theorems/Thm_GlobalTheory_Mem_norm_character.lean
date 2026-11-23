-- Prove2me | Theorems.Thm_GlobalTheory_Mem_norm_character
-- name    : GlobalTheory.Mem.norm_character
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:49.503264+00:00
-- url     : https://prove2.me/theorems/8725a9fd-1750-41e3-bcdc-fe9970c23e34
-- title:
--   Mem: norm character
-- statement:
--   The Mem construction uses the norm character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean#L150-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean#L150-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem

theorem GlobalTheory.Mem.norm_character {G : Type} [CommGroup G] [Fintype G] (χ : G →* ℂˣ) (g : G) :
    ‖(χ g : ℂ)‖ = 1 := by sorry
