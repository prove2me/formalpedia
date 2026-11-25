-- Prove2me | Theorems.Thm_GroundTheory_Global_finite_setOf_ramificationIdx_ne_one
-- name    : GroundTheory.Global.finite_setOf_ramificationIdx_ne_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:14:48.2001+00:00
-- url     : https://prove2.me/theorems/8d223c4a-6add-4ad8-a980-c5f6527219fa
-- title:
--   Global: finite set Of ramification Idx ne one
-- statement:
--   The Global construction uses the finite set Of ramification Idx ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L346-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L346-L349

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

theorem GroundTheory.Global.finite_setOf_ramificationIdx_ne_one :
    {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite := by sorry
