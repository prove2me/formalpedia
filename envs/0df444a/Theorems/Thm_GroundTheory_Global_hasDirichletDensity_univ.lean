-- Prove2me | Theorems.Thm_GroundTheory_Global_hasDirichletDensity_univ
-- name    : GroundTheory.Global.hasDirichletDensity_univ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:17.7878+00:00
-- url     : https://prove2.me/theorems/08cb649a-1606-4e84-b68b-77864589e643
-- title:
--   Global: has Dirichlet Density univ
-- statement:
--   The Global construction uses the has Dirichlet Density univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L48-L52

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
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.hasDirichletDensity_univ : (univ : Set (HeightOneSpectrum (𝓞 K))).HasDirichletDensity 1 := by sorry
