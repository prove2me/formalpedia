-- Prove2me | Theorems.Thm_GroundTheory_Global_valued_trace_le_one_of_valuation_le_one
-- name    : GroundTheory.Global.valued_trace_le_one_of_valuation_le_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:33:18.837411+00:00
-- url     : https://prove2.me/theorems/69cd9861-8133-4c86-92b5-3d71a339b66f
-- title:
--   Global: valued trace le one of valuation le one
-- statement:
--   The Global construction uses the valued trace le one of valuation le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L186-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L186-L192

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
open SemiLocal
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem GroundTheory.Global.valued_trace_le_one_of_valuation_le_one (v : HeightOneSpectrum (𝓞 K))
    (u : PlacesOver M v) {x : M} (hx : u.1.valuation M x ≤ 1) :
    Valued.v (Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
      (algebraMap M (u.1.adicCompletion M) x)) ≤ 1 := by sorry
