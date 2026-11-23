-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_maximalIdeal_iff_valued_lt_one
-- name    : GroundTheory.Global.mem_maximalIdeal_iff_valued_lt_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:27.581584+00:00
-- url     : https://prove2.me/theorems/fab0b0dd-a063-436f-bcb0-1aa9c0f54edc
-- title:
--   Global: mem maximal Ideal iff valued lt one
-- statement:
--   The Global construction uses the mem maximal Ideal iff valued lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Integers.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Integers.lean#L152-L156

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
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
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem GroundTheory.Global.mem_maximalIdeal_iff_valued_lt_one (y : 𝒪[u.adicCompletion F]) :
    y ∈ 𝓂[u.adicCompletion F] ↔ Valued.v (y : u.adicCompletion F) < 1 := by sorry
