-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_sUnitsOf
-- name    : GroundTheory.ProfCoh.mem_sUnitsOf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:04.07517+00:00
-- url     : https://prove2.me/theorems/3fbca578-9fd5-4128-a21a-69c660d2dc21
-- title:
--   Prof Coh: mem s Units Of
-- statement:
--   The Prof Coh construction uses the mem s Units Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SUnitsDefs.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SUnitsDefs.lean#L36-L39

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SUnitsDefs
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
open NumberField IsDedekindDomain CategoryTheory
universe u
variable {F : Type u} [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable (E : Type u) [Field E] [Algebra F E]
variable {S E}

theorem GroundTheory.ProfCoh.mem_sUnitsOf {x : Eˣ} :
    x ∈ sUnitsOf S E ↔
      IsIntegral (S.integer F) (x : E) ∧ IsIntegral (S.integer F) ((x⁻¹ : Eˣ) : E) := by sorry
