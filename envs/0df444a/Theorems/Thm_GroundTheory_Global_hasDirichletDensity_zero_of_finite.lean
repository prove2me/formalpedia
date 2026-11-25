-- Prove2me | Theorems.Thm_GroundTheory_Global_hasDirichletDensity_zero_of_finite
-- name    : GroundTheory.Global.hasDirichletDensity_zero_of_finite
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:56:00.274112+00:00
-- url     : https://prove2.me/theorems/a0446195-6d45-4414-93e8-97ec42d4847f
-- title:
--   Global: has Dirichlet Density zero of finite
-- statement:
--   The Global construction uses the has Dirichlet Density zero of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L320-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L320-L322

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
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
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]

theorem GroundTheory.Global.hasDirichletDensity_zero_of_finite {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) : S.HasDirichletDensity 0 := by sorry
