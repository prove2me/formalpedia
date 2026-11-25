-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_iff_forall_mem_localIdeal
-- name    : GroundTheory.Global.mem_iff_forall_mem_localIdeal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:39:25.406803+00:00
-- url     : https://prove2.me/theorems/515ee94d-b2b8-433d-9590-c2957c20d159
-- title:
--   Global: mem iff forall mem local Ideal
-- statement:
--   The Global construction uses the mem iff forall mem local Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L118-L122

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
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
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.mem_iff_forall_mem_localIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {x : K} :
    x ∈ I ↔ ∀ v : HeightOneSpectrum (𝓞 K), (x : v.adicCompletion K) ∈ localIdeal I v := by sorry
