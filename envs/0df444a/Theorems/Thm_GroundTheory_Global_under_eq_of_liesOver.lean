-- Prove2me | Theorems.Thm_GroundTheory_Global_under_eq_of_liesOver
-- name    : GroundTheory.Global.under_eq_of_liesOver
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:44.836368+00:00
-- url     : https://prove2.me/theorems/72fc325d-79ad-4b64-a247-a9601eb1582d
-- title:
--   Global: under eq of lies Over
-- statement:
--   The Global construction uses the under eq of lies Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/BadPrimesFinite.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/BadPrimesFinite.lean#L14-L16

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_FunctionFieldIntegral
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_BadPrimesFinite
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
open NumberField IsDedekindDomain IsLocalRing WeierstrassCurve.Affine
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.under_eq_of_liesOver {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (h : w.asIdeal.LiesOver v.asIdeal) : w.under (𝓞 K) = v := by sorry
