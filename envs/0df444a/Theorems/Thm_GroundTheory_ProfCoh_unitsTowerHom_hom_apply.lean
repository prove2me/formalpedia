-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_unitsTowerHom_hom_apply
-- name    : GroundTheory.ProfCoh.unitsTowerHom_hom_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:16:50.984023+00:00
-- url     : https://prove2.me/theorems/673b7cef-9614-4265-895f-4ebbdd22db7d
-- title:
--   Prof Coh: units Tower Hom hom apply
-- statement:
--   The Prof Coh construction uses the units Tower Hom hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisCohomology/BrauerInflationDefs.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisCohomology/BrauerInflationDefs.lean#L25-L28

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
variable (K E F : Type u) [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [Normal K E]

theorem GroundTheory.ProfCoh.unitsTowerHom_hom_apply (x : Additive Eˣ) :
    ((Additive.toMul (α := Fˣ) ((unitsTowerHom K E F).hom x) : Fˣ) : F) =
      algebraMap E F ((Additive.toMul (α := Eˣ) x : Eˣ) : E) := by sorry

attribute [defeq] GroundTheory.ProfCoh.unitsTowerHom_hom_apply
