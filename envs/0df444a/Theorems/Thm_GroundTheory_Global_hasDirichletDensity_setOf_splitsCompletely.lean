-- Prove2me | Theorems.Thm_GroundTheory_Global_hasDirichletDensity_setOf_splitsCompletely
-- name    : GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:55:37.967459+00:00
-- url     : https://prove2.me/theorems/ff36fd16-47fb-5ab0-8e5f-ffa4d283d01c
-- title:
--   Global: has Dirichlet Density set Of splits Completely
-- statement:
--   The Global construction uses the has Dirichlet Density set Of splits Completely property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L353-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L353-L375

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
variable (K L)

theorem GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely [IsGalois K L] :
    {v : HeightOneSpectrum (𝓞 K) | SplitsCompletely L v}.HasDirichletDensity
      (1 / Module.finrank K L) := by sorry
