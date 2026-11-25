-- Prove2me | Theorems.Thm_GroundTheory_Global_finite_mulSupport_nnnorm_units
-- name    : GroundTheory.Global.finite_mulSupport_nnnorm_units
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:13:48.20595+00:00
-- url     : https://prove2.me/theorems/33f0eb45-a34b-4120-9c7f-d9d3761383a3
-- title:
--   Global: finite mul Support nnnorm units
-- statement:
--   The Global construction uses the finite mul Support nnnorm units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L110-L113

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.finite_mulSupport_nnnorm_units (u : (𝔸ᶠ[K])ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(u : 𝔸ᶠ[K]) v‖₊).Finite := by sorry
