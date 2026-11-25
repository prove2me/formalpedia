-- Prove2me | Theorems.Thm_GroundTheory_Global_hasDirichletDensity_degreeOnePrimes
-- name    : GroundTheory.Global.hasDirichletDensity_degreeOnePrimes
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:24.417064+00:00
-- url     : https://prove2.me/theorems/78670b3f-6e8d-46d9-abc5-4d5fd015f5f3
-- title:
--   Global: has Dirichlet Density degree One Primes
-- statement:
--   The Global construction uses the has Dirichlet Density degree One Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L106-L109

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
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (K L)

theorem GroundTheory.Global.hasDirichletDensity_degreeOnePrimes : (degreeOnePrimes K L).HasDirichletDensity 1 := by sorry
