-- Prove2me | Theorems.Thm_GroundTheory_Global_not_isEquiv_adicAbv
-- name    : GroundTheory.Global.not_isEquiv_adicAbv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:08.680736+00:00
-- url     : https://prove2.me/theorems/8d4f2e24-a232-4f13-9669-e134d7b437d0
-- title:
--   Global: not is Equiv adic Abv
-- statement:
--   The Global construction uses the not is Equiv adic Abv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean#L22-L30

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

theorem GroundTheory.Global.not_isEquiv_adicAbv {v v' : HeightOneSpectrum (𝓞 K)} (h : v ≠ v') :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv (NumberField.HeightOneSpectrum.adicAbv K v') := by sorry
