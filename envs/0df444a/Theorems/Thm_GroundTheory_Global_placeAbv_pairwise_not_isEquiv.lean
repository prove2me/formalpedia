-- Prove2me | Theorems.Thm_GroundTheory_Global_placeAbv_pairwise_not_isEquiv
-- name    : GroundTheory.Global.placeAbv_pairwise_not_isEquiv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:11.513581+00:00
-- url     : https://prove2.me/theorems/d97e9afb-de40-4295-b5d4-f09f6b988ef1
-- title:
--   Global: place Abv pairwise not is Equiv
-- statement:
--   The Global construction uses the place Abv pairwise not is Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean#L57-L65

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

theorem GroundTheory.Global.placeAbv_pairwise_not_isEquiv :
    Pairwise fun i j ↦ ¬ (placeAbv S T i).IsEquiv (placeAbv S T j) := by sorry
