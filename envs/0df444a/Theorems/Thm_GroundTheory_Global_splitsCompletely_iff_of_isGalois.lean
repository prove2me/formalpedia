-- Prove2me | Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_of_isGalois
-- name    : GroundTheory.Global.splitsCompletely_iff_of_isGalois
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:39.521154+00:00
-- url     : https://prove2.me/theorems/65aac152-0178-4f49-a432-f0c5fee02960
-- title:
--   Global: splits Completely iff of is Galois
-- statement:
--   The Global construction uses the splits Completely iff of is Galois property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L195-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L195-L206

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
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.splitsCompletely_iff_of_isGalois [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [hw : w.asIdeal.LiesOver v.asIdeal] :
    SplitsCompletely L v ↔
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1 := by sorry
