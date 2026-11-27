-- Prove2me | Theorems.Thm_GroundTheory_Global_localFactor_eq
-- name    : GroundTheory.Global.localFactor_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:55:37.734055+00:00
-- url     : https://prove2.me/theorems/97ad6287-e375-5a37-aa9e-ee215a66c6f0
-- title:
--   Global: local Factor eq
-- statement:
--   The Global construction uses the local Factor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L239-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L239-L242

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

theorem GroundTheory.Global.localFactor_eq (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    {φ : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal) :
    localFactor v ρ = inertiaFactor ρ w φ hφ.mem_stabilizer := by sorry
