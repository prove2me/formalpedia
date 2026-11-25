-- Prove2me | Theorems.Thm_GroundTheory_Global_eventually_mem_localizationAt
-- name    : GroundTheory.Global.eventually_mem_localizationAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:36.751427+00:00
-- url     : https://prove2.me/theorems/d5f8c9eb-837c-4a22-a3eb-8de7e84679e9
-- title:
--   Global: eventually mem localization At
-- statement:
--   The Global construction uses the eventually mem localization At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/PrimeLocalization.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/PrimeLocalization.lean#L35-L41

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
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
open NumberField IsDedekindDomain Polynomial
noncomputable section
variable (L : Type*) [Field L] [NumberField L]
variable {L}

theorem GroundTheory.Global.eventually_mem_localizationAt (x : L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite, x ∈ localizationAt L v := by sorry
