-- Prove2me | Theorems.Thm_GroundTheory_Global_eventually_exists_map_eq
-- name    : GroundTheory.Global.eventually_exists_map_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:40:15.50396+00:00
-- url     : https://prove2.me/theorems/25e0862b-c7f5-4827-8936-44d74fefd074
-- title:
--   Global: eventually exists map eq
-- statement:
--   The Global construction uses the eventually exists map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean#L12-L19

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
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
open NumberField IsDedekindDomain IsLocalRing
noncomputable section
variable {L : Type*} [Field L] [NumberField L]

theorem GroundTheory.Global.eventually_exists_map_eq (E : WeierstrassCurve L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L v),
        W.map (algebraMap (localizationAt L v) L) = E := by sorry
