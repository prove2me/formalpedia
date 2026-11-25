-- Prove2me | Theorems.Thm_GroundTheory_Global_primeIdealZetaSum_mono
-- name    : GroundTheory.Global.primeIdealZetaSum_mono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:48.213495+00:00
-- url     : https://prove2.me/theorems/7d110ec3-b7cb-4d19-bebb-d889a9255801
-- title:
--   Global: prime Ideal Zeta Sum mono
-- statement:
--   The Global construction uses the prime Ideal Zeta Sum mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L16-L24

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

theorem GroundTheory.Global.primeIdealZetaSum_mono {A B : Set (HeightOneSpectrum (𝓞 K))} (hAB : A ⊆ B) {s : ℝ}
    (hs : 1 < s) : A.primeIdealZetaSum s ≤ B.primeIdealZetaSum s := by sorry
