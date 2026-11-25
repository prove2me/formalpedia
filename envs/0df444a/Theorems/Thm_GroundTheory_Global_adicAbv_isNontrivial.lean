-- Prove2me | Theorems.Thm_GroundTheory_Global_adicAbv_isNontrivial
-- name    : GroundTheory.Global.adicAbv_isNontrivial
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:43.921824+00:00
-- url     : https://prove2.me/theorems/be3264b7-5eaf-4872-9b3a-270efa9afadb
-- title:
--   Global: adic Abv is Nontrivial
-- statement:
--   The Global construction uses the adic Abv is Nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean#L16-L20

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

theorem GroundTheory.Global.adicAbv_isNontrivial (v : HeightOneSpectrum (𝓞 K)) : (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by sorry
