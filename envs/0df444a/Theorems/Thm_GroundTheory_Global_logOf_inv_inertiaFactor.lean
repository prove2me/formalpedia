-- Prove2me | Theorems.Thm_GroundTheory_Global_logOf_inv_inertiaFactor
-- name    : GroundTheory.Global.logOf_inv_inertiaFactor
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:35.102897+00:00
-- url     : https://prove2.me/theorems/2cec728d-e834-4226-bfdb-2d217bf4e091
-- title:
--   Global: log Of inv inertia Factor
-- statement:
--   The Global construction uses the log Of inv inertia Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L225-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L225-L233

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
omit [IsGalois K L]

theorem GroundTheory.Global.logOf_inv_inertiaFactor (w : HeightOneSpectrum (𝓞 L)) {φ : Gal(L/K)}
    (hφ : φ ∈ MulAction.stabilizer Gal(L/K) w.asIdeal) :
    PowerSeries.logOf ((inertiaFactor ρ w φ hφ : PowerSeries ℂ)⁻¹) =
      PowerSeries.mk fun m => if m = 0 then 0 else
        cosetAverage (w.asIdeal.inertia Gal(L/K)) ρ.character (φ ^ m) / m := by sorry
