-- Prove2me | Theorems.Thm_Neutral_B1_exists_isUniformiserAt
-- name    : Neutral.B1.exists_isUniformiserAt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:46.162799+00:00
-- url     : https://prove2.me/theorems/3da9f54f-d532-4962-9312-0854f8a21f52
-- title:
--   B1: exists is Uniformiser At
-- statement:
--   The B1 construction uses the exists is Uniformiser At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L274-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean#L274-L280

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Topology
open Neutral Neutral.B1
variable (K : Type*) [Field K] [NumberField K]

theorem Neutral.B1.exists_isUniformiserAt (v : HeightOneSpectrum (𝓞 K)) :
    ∃ π : (v.adicCompletion K)ˣ, IsUniformiserAt K v (π : v.adicCompletion K) := by sorry
