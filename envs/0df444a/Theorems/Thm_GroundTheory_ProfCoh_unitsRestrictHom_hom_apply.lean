-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_unitsRestrictHom_hom_apply
-- name    : GroundTheory.ProfCoh.unitsRestrictHom_hom_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:16.536118+00:00
-- url     : https://prove2.me/theorems/b3243d92-ec49-4a08-b4cd-8ee275c456f8
-- title:
--   Prof Coh: units Restrict Hom hom apply
-- statement:
--   The Prof Coh construction uses the units Restrict Hom hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisCohomology/UnitsInflationCochainsFHomApply.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisCohomology/UnitsInflationCochainsFHomApply.lean#L86-L90

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply
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
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable {K L}

theorem GroundTheory.ProfCoh.unitsRestrictHom_hom_apply (E : IntermediateField K L) [Normal K E]
    (x : Additive Eˣ) :
    ((Additive.toMul (α := Lˣ) ((unitsRestrictHom E).hom x) : Lˣ) : L) =
      ((Additive.toMul (α := Eˣ) x : Eˣ) : E) := by sorry

attribute [defeq] GroundTheory.ProfCoh.unitsRestrictHom_hom_apply
