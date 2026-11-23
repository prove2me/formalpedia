-- Prove2me | Theorems.Thm_GroundTheory_Global_norm_natCast_adicCompletion_eq_one
-- name    : GroundTheory.Global.norm_natCast_adicCompletion_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:53.155815+00:00
-- url     : https://prove2.me/theorems/033b4edc-aab9-4ae5-b9bb-ff849b02232e
-- title:
--   Global: norm nat Cast adic Completion eq one
-- statement:
--   The Global construction uses the norm nat Cast adic Completion eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexProductFormula.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexProductFormula.lean#L9-L12

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

theorem GroundTheory.Global.norm_natCast_adicCompletion_eq_one {v : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (hv : (n : 𝓞 K) ∉ v.asIdeal) : ‖(n : v.adicCompletion K)‖ = 1 := by sorry
