-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_sub_ringOfIntegersToInteger_mem
-- name    : GroundTheory.Global.exists_sub_ringOfIntegersToInteger_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:01:49.096381+00:00
-- url     : https://prove2.me/theorems/d1af9fbf-ca13-41c5-83ca-c104f6b86323
-- title:
--   Global: exists sub ring Of Integers To Integer mem
-- statement:
--   The Global construction uses the exists sub ring Of Integers To Integer mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Inertia.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Inertia.lean#L18-L21

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Inertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem GroundTheory.Global.exists_sub_ringOfIntegersToInteger_mem (x : 𝒪[u.adicCompletion F]) :
    ∃ r : 𝓞 F, x - ringOfIntegersToInteger u r ∈ 𝓂[u.adicCompletion F] := by sorry
