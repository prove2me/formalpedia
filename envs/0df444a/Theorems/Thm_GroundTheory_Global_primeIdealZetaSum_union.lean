-- Prove2me | Theorems.Thm_GroundTheory_Global_primeIdealZetaSum_union
-- name    : GroundTheory.Global.primeIdealZetaSum_union
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:27.046096+00:00
-- url     : https://prove2.me/theorems/0725fa35-80c9-4f6c-8b7e-0af826620a09
-- title:
--   Global: prime Ideal Zeta Sum union
-- statement:
--   The Global construction uses the prime Ideal Zeta Sum union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L26-L32

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

theorem GroundTheory.Global.primeIdealZetaSum_union {A B : Set (HeightOneSpectrum (𝓞 K))} (hd : Disjoint A B)
    {s : ℝ} (hs : 1 < s) :
    (A ∪ B).primeIdealZetaSum s = A.primeIdealZetaSum s + B.primeIdealZetaSum s := by sorry
