-- Prove2me | Theorems.Thm_GroundTheory_Global_normalizedAbv_of_irreducible
-- name    : GroundTheory.Global.normalizedAbv_of_irreducible
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:35.256465+00:00
-- url     : https://prove2.me/theorems/16d0925d-0502-4f3d-9e36-a1bd52c31679
-- title:
--   Global: normalized Abv of irreducible
-- statement:
--   The Global construction uses the normalized Abv of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L63-L68

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
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.normalizedAbv_of_irreducible {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    normalizedAbv v (ϖ : v.adicCompletion K) = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by sorry
