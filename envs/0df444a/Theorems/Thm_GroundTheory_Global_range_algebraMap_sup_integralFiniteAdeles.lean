-- Prove2me | Theorems.Thm_GroundTheory_Global_range_algebraMap_sup_integralFiniteAdeles
-- name    : GroundTheory.Global.range_algebraMap_sup_integralFiniteAdeles
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:22.418795+00:00
-- url     : https://prove2.me/theorems/df163329-6752-4fd6-be7f-ab265bb3604e
-- title:
--   Global: range algebra Map sup integral Finite Adeles
-- statement:
--   The Global construction uses the range algebra Map sup integral Finite Adeles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Approximation.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Approximation.lean#L72-L80

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsValuationSubLeOne
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem GroundTheory.Global.range_algebraMap_sup_integralFiniteAdeles :
    (algebraMap K (FiniteAdeleRing R K)).range.toAddSubgroup ⊔
      (integralFiniteAdeles R K).toAddSubgroup = ⊤ := by sorry
