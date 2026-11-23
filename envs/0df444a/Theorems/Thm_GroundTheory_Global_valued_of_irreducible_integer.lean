-- Prove2me | Theorems.Thm_GroundTheory_Global_valued_of_irreducible_integer
-- name    : GroundTheory.Global.valued_of_irreducible_integer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:38.837813+00:00
-- url     : https://prove2.me/theorems/d7320ea8-6bfc-4a26-9e66-ca1bd6a6c28c
-- title:
--   Global: valued of irreducible integer
-- statement:
--   The Global construction uses the valued of irreducible integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Integers.lean#L158-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Integers.lean#L158-L178

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

theorem GroundTheory.Global.valued_of_irreducible_integer {ϖ : 𝒪[u.adicCompletion F]} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : u.adicCompletion F) = WithZero.exp (-1) := by sorry
