-- Prove2me | Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- name    : GroundTheory.Global.residueFieldEquiv_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:37.051928+00:00
-- url     : https://prove2.me/theorems/6208079f-5114-447f-bdaf-294f685f875d
-- title:
--   Global: residue Field Equiv mk
-- statement:
--   The Global construction uses the residue Field Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalAtPlace.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalAtPlace.lean#L77-L80

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open GroundTheory GroundTheory.Global
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem GroundTheory.Global.residueFieldEquiv_mk (r : R) :
    residueFieldEquiv (K := K) v (Ideal.Quotient.mk v.asIdeal r) =
      IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) := by sorry

attribute [defeq] GroundTheory.Global.residueFieldEquiv_mk
