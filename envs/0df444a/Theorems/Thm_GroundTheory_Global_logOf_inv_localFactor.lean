-- Prove2me | Theorems.Thm_GroundTheory_Global_logOf_inv_localFactor
-- name    : GroundTheory.Global.logOf_inv_localFactor
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:55:43.612581+00:00
-- url     : https://prove2.me/theorems/ad41ca90-022a-51b8-b9a6-fea5ccebdc24
-- title:
--   Global: log Of inv local Factor
-- statement:
--   The Global construction uses the log Of inv local Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L244-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L244-L247

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

theorem GroundTheory.Global.logOf_inv_localFactor :
    PowerSeries.logOf ((localFactor v ρ : PowerSeries ℂ)⁻¹) =
      PowerSeries.mk fun m => if m = 0 then 0 else localAverage L v ρ.character m / m := by sorry
