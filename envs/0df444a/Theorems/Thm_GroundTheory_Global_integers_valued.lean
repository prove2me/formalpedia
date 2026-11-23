-- Prove2me | Theorems.Thm_GroundTheory_Global_integers_valued
-- name    : GroundTheory.Global.integers_valued
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:47:31.631736+00:00
-- url     : https://prove2.me/theorems/4f099624-0782-4cc2-a686-d78e3195c1d4
-- title:
--   Global: integers valued
-- statement:
--   The Global construction uses the integers valued property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Integers.lean#L143-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Integers.lean#L143-L150

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

theorem GroundTheory.Global.integers_valued :
    (Valued.v : Valuation (u.adicCompletion F) ℤᵐ⁰).Integers 𝒪[u.adicCompletion F] := by sorry
