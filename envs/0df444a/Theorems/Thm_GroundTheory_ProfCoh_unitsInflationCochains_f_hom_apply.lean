-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_unitsInflationCochains_f_hom_apply
-- name    : GroundTheory.ProfCoh.unitsInflationCochains_f_hom_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:56:50.992897+00:00
-- url     : https://prove2.me/theorems/1db90107-aa4f-417f-b1a6-4b521077ce70
-- title:
--   Prof Coh: units Inflation Cochains f hom apply
-- statement:
--   The Prof Coh construction uses the units Inflation Cochains f hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisCohomology/UnitsInflationCochainsFHomApply.lean#L132-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GaloisCohomology/UnitsInflationCochainsFHomApply.lean#L132-L136

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
variable [IsGalois K L]

theorem GroundTheory.ProfCoh.unitsInflationCochains_f_hom_apply (E : IntermediateField K L) [FiniteDimensional K E]
    [Normal K E] (n : ℕ) (x : (Fin n → Gal(E/K)) → Additive Eˣ) (g : Fin n → Gal(L/K)) :
    ((cochainsComplexι (galUnits.{u} K L)).f n).hom (((unitsInflationCochains E).f n).hom x) g =
      (unitsRestrictHom E).hom (x fun i => AlgEquiv.restrictNormalHom E (g i)) := by sorry

attribute [defeq] GroundTheory.ProfCoh.unitsInflationCochains_f_hom_apply
