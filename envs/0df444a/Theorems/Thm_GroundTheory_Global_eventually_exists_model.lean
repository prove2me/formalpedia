-- Prove2me | Theorems.Thm_GroundTheory_Global_eventually_exists_model
-- name    : GroundTheory.Global.eventually_exists_model
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:40:31.160866+00:00
-- url     : https://prove2.me/theorems/8e4ec524-dee5-482f-b00a-310387f867be
-- title:
--   Global: eventually exists model
-- statement:
--   The Global construction uses the eventually exists model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean#L32-L37

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

theorem GroundTheory.Global.eventually_exists_model (E : WeierstrassCurve L) [E.IsElliptic] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L v),
        W.IsElliptic ∧ W.map (algebraMap (localizationAt L v) L) = E := by sorry
