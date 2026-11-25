-- Prove2me | Theorems.Thm_GroundTheory_Global_multiplicity_relDiscr_semiLocal
-- name    : GroundTheory.Global.multiplicity_relDiscr_semiLocal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:57:39.655906+00:00
-- url     : https://prove2.me/theorems/a990972b-8ebe-49a0-9c29-1c97cab9f7e2
-- title:
--   Global: multiplicity rel Discr semi Local
-- statement:
--   The Global construction uses the multiplicity rel Discr semi Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L340-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L340-L346

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
open SemiLocal

theorem GroundTheory.Global.multiplicity_relDiscr_semiLocal (v : HeightOneSpectrum (𝓞 K)) :
    multiplicity v.asIdeal (relDiscr K M) =
      ∑ w : PlacesOver M v, w.1.asIdeal.inertiaDeg (𝓞 K) *
        differentExponent (v.adicCompletion K) (w.1.adicCompletion M) := by sorry
