-- Prove2me | Theorems.Thm_GroundTheory_Global_hasDirichletDensity_zero_of_isBoundedUnder
-- name    : GroundTheory.Global.hasDirichletDensity_zero_of_isBoundedUnder
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:53:41.616801+00:00
-- url     : https://prove2.me/theorems/4158f91f-1e13-56a1-b46e-45a0c5fdd8cd
-- title:
--   Global: has Dirichlet Density zero of is Bounded Under
-- statement:
--   The Global construction uses the has Dirichlet Density zero of is Bounded Under property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L34-L46

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

theorem GroundTheory.Global.hasDirichletDensity_zero_of_isBoundedUnder {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s => S.primeIdealZetaSum s) :
    S.HasDirichletDensity 0 := by sorry
