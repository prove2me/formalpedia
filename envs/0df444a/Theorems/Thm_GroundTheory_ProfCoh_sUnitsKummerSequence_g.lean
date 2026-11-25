-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_sUnitsKummerSequence_g
-- name    : GroundTheory.ProfCoh.sUnitsKummerSequence_g
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:26.421146+00:00
-- url     : https://prove2.me/theorems/5596eab9-3292-5af4-8840-c9798aa53ade
-- title:
--   Prof Coh: s Units Kummer Sequence g
-- statement:
--   The Prof Coh construction uses the s Units Kummer Sequence g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SUnitsDefs.lean#L132-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SUnitsDefs.lean#L132-L133

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
variable (S E)
variable (n : ℕ) [NeZero n]

theorem GroundTheory.ProfCoh.sUnitsKummerSequence_g : (sUnitsKummerSequence S E n).g = n • 𝟙 (galSUnits S E) := by sorry
