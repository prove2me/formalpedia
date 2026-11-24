-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coe_unitsOfLE_hom_apply
-- name    : GroundTheory.ProfCoh.coe_unitsOfLE_hom_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:17:25.686254+00:00
-- url     : https://prove2.me/theorems/a7278e71-5002-4023-b83b-2409dd126778
-- title:
--   Prof Coh: coe units Of LE hom apply
-- statement:
--   The Prof Coh construction uses the coe units Of LE hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisCohomology/BrauerInflationDefs.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisCohomology/BrauerInflationDefs.lean#L59-L62

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_BrauerInflationDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] {E F : IntermediateField K L}
  (h : E ≤ F) [Normal K E]

theorem GroundTheory.ProfCoh.coe_unitsOfLE_hom_apply (x : Additive Eˣ) :
    (((Additive.toMul (α := Fˣ) ((unitsOfLE h).hom x) : Fˣ) : F) : L) =
      (((Additive.toMul (α := Eˣ) x : Eˣ) : E) : L) := by sorry

attribute [defeq] GroundTheory.ProfCoh.coe_unitsOfLE_hom_apply
