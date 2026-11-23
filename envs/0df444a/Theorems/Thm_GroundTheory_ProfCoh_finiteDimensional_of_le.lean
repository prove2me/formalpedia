-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finiteDimensional_of_le
-- name    : GroundTheory.ProfCoh.finiteDimensional_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:45.463036+00:00
-- url     : https://prove2.me/theorems/e69a13bc-489b-4a14-bbe6-bcc014f51d29
-- title:
--   Prof Coh: finite Dimensional of le
-- statement:
--   The Prof Coh construction uses the finite Dimensional of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/Unramified.lean#L16-L19

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
omit [NumberField F]

theorem GroundTheory.ProfCoh.finiteDimensional_of_le {E M : IntermediateField F Ω} (h : E ≤ M) [FiniteDimensional F M] :
    FiniteDimensional F E := by sorry
