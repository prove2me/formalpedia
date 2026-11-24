-- Prove2me | Theorems.Thm_GroundTheory_Global_placeAbv_isNontrivial
-- name    : GroundTheory.Global.placeAbv_isNontrivial
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:41:59.783812+00:00
-- url     : https://prove2.me/theorems/c65e8b71-9824-4b76-b3ac-f69306b4ba1d
-- title:
--   Global: place Abv is Nontrivial
-- statement:
--   The Global construction uses the place Abv is Nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean#L53-L55

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApprox
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
open IsDedekindDomain NumberField
variable {K : Type*} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))

theorem GroundTheory.Global.placeAbv_isNontrivial : ∀ i, (placeAbv S T i).IsNontrivial
  := by sorry
