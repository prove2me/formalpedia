-- Prove2me | Theorems.Thm_GroundTheory_Global_prod_norm_natCast_mul_prod_infinitePlace
-- name    : GroundTheory.Global.prod_norm_natCast_mul_prod_infinitePlace
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:17.429534+00:00
-- url     : https://prove2.me/theorems/1c7ad6b3-c596-49e9-943c-fdf79e99cb37
-- title:
--   Global: prod norm nat Cast mul prod infinite Place
-- statement:
--   The Global construction uses the prod norm nat Cast mul prod infinite Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexProductFormula.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexProductFormula.lean#L45-L50

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
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
open NumberField IsDedekindDomain
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.prod_norm_natCast_mul_prod_infinitePlace {n : ℕ} (hn : n ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, ‖(n : v.adicCompletion K)‖) *
      ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult = 1 := by sorry
