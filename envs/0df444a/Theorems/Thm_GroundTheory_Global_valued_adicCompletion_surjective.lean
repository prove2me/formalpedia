-- Prove2me | Theorems.Thm_GroundTheory_Global_valued_adicCompletion_surjective
-- name    : GroundTheory.Global.valued_adicCompletion_surjective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:15.943297+00:00
-- url     : https://prove2.me/theorems/ef657b7f-9cbb-47af-b6f1-446be0fd1029
-- title:
--   Global: valued adic Completion surjective
-- statement:
--   The Global construction uses the valued adic Completion surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L19-L21

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
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem GroundTheory.Global.valued_adicCompletion_surjective :
    Function.Surjective (Valued.v : v.adicCompletion K → ℤᵐ⁰) := by sorry
