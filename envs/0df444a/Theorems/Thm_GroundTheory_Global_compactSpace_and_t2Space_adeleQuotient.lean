-- Prove2me | Theorems.Thm_GroundTheory_Global_compactSpace_and_t2Space_adeleQuotient
-- name    : GroundTheory.Global.compactSpace_and_t2Space_adeleQuotient
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:06.581574+00:00
-- url     : https://prove2.me/theorems/f4ba4224-a8b2-5c5e-84d0-6d7f0560763b
-- title:
--   Global: compact Space and t2 Space adele Quotient
-- statement:
--   The Global construction uses the compact Space and t2 Space adele Quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Compact.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Compact.lean#L47-L50

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
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
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.compactSpace_and_t2Space_adeleQuotient :
    CompactSpace (𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K) ∧
      T2Space (𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K) := by sorry
