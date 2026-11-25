-- Prove2me | Theorems.Thm_GroundTheory_Global_eq_placeBelow_of_liesOver
-- name    : GroundTheory.Global.eq_placeBelow_of_liesOver
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:48:08.718967+00:00
-- url     : https://prove2.me/theorems/075d625b-8bb6-4bce-b135-9969a7aa428f
-- title:
--   Global: eq place Below of lies Over
-- statement:
--   The Global construction uses the eq place Below of lies Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean#L95-L97

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
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
open MulAction NumberField IsDedekindDomain
open scoped Pointwise
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
omit [NumberField K] [NumberField L] [IsGalois K L]

theorem GroundTheory.Global.eq_placeBelow_of_liesOver {w : HeightOneSpectrum (𝓞 L)} {v : HeightOneSpectrum (𝓞 K)}
    (h : w.asIdeal.LiesOver v.asIdeal) : v = placeBelow w := by sorry
