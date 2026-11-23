-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_integralFiniteAdeles
-- name    : GroundTheory.Global.mem_integralFiniteAdeles
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:28.401521+00:00
-- url     : https://prove2.me/theorems/f8e17461-f715-4ac5-988a-a3bcebd4537f
-- title:
--   Global: mem integral Finite Adeles
-- statement:
--   The Global construction uses the mem integral Finite Adeles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Approximation.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Approximation.lean#L26-L28

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

theorem GroundTheory.Global.mem_integralFiniteAdeles {a : FiniteAdeleRing R K} :
    a ∈ integralFiniteAdeles R K ↔ ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K := by sorry
