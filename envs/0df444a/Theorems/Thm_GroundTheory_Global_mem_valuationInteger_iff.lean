-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff
-- name    : GroundTheory.Global.mem_valuationInteger_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:39.801361+00:00
-- url     : https://prove2.me/theorems/bf82789e-6513-4ae7-a64c-6c8b3acf8e89
-- title:
--   Global: mem valuation Integer iff
-- statement:
--   The Global construction uses the mem valuation Integer iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L98-L101

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero
open scoped WithZero
open GroundTheory GroundTheory.Global
open ValuativeRel
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem GroundTheory.Global.mem_valuationInteger_iff (x : v.adicCompletion K) :
    x ∈ 𝒪[v.adicCompletion K] ↔ x ∈ v.adicCompletionIntegers K := by sorry
