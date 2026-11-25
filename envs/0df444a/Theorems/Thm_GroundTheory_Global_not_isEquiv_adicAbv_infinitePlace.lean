-- Prove2me | Theorems.Thm_GroundTheory_Global_not_isEquiv_adicAbv_infinitePlace
-- name    : GroundTheory.Global.not_isEquiv_adicAbv_infinitePlace
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:11.217424+00:00
-- url     : https://prove2.me/theorems/1bc73ee7-64af-4b04-967a-199b59c09d07
-- title:
--   Global: not is Equiv adic Abv infinite Place
-- statement:
--   The Global construction uses the not is Equiv adic Abv infinite Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean#L32-L42

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

theorem GroundTheory.Global.not_isEquiv_adicAbv_infinitePlace (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by sorry
