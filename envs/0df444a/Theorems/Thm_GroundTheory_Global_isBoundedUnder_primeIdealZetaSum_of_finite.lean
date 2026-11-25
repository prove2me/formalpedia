-- Prove2me | Theorems.Thm_GroundTheory_Global_isBoundedUnder_primeIdealZetaSum_of_finite
-- name    : GroundTheory.Global.isBoundedUnder_primeIdealZetaSum_of_finite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:54:30.375749+00:00
-- url     : https://prove2.me/theorems/11b2ef2e-c814-5da3-bafa-c0a6a122d6d9
-- title:
--   Global: is Bounded Under prime Ideal Zeta Sum of finite
-- statement:
--   The Global construction uses the is Bounded Under prime Ideal Zeta Sum of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L314-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L314-L318

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

theorem GroundTheory.Global.isBoundedUnder_primeIdealZetaSum_of_finite {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) :
    IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s => S.primeIdealZetaSum s := by sorry
