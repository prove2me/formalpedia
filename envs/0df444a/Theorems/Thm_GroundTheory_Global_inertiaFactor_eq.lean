-- Prove2me | Theorems.Thm_GroundTheory_Global_inertiaFactor_eq
-- name    : GroundTheory.Global.inertiaFactor_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:33.598815+00:00
-- url     : https://prove2.me/theorems/872adf64-285b-4fe6-a678-b35fe37b95e4
-- title:
--   Global: inertia Factor eq
-- statement:
--   The Global construction uses the inertia Factor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L215-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L215-L221

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Polynomial
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K L V : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : Representation ℂ Gal(L/K) V)

theorem GroundTheory.Global.inertiaFactor_eq (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    [w'.asIdeal.LiesOver v.asIdeal] {φ φ' : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal)
    (hφ' : IsArithFrobAt (𝓞 K) φ' w'.asIdeal) :
    inertiaFactor ρ w φ hφ.mem_stabilizer = inertiaFactor ρ w' φ' hφ'.mem_stabilizer := by sorry
