-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_of_moduleFinite
-- name    : GroundTheory.ProfCoh.finite_torsN_of_moduleFinite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:24:11.072259+00:00
-- url     : https://prove2.me/theorems/64a90003-a589-401f-831f-24e5deacf174
-- title:
--   Prof Coh: finite tors N of module Finite
-- statement:
--   The Prof Coh construction uses the finite tors N of module Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/GEqAddOfExactOfFiniteCokernel.lean#L28-L38

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_UnitsDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_GEqAddOfExactOfFiniteCokernel
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
universe u v
open NumberField NumberField.Units NumberField.InfinitePlace IsDedekindDomain Module
open GroundTheory.Global
open scoped TensorProduct
variable {A : Type*} [AddCommGroup A] [Module.Finite ℤ A] (n : ℕ) [NeZero n]

theorem GroundTheory.ProfCoh.finite_torsN_of_moduleFinite : Finite (TorsN A n) := by sorry
