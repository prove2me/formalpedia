-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_isCompact_forall_exists_sub_mem
-- name    : GroundTheory.Global.exists_isCompact_forall_exists_sub_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:23.496608+00:00
-- url     : https://prove2.me/theorems/35d9ad1c-f184-4947-84c8-6a8373b4306c
-- title:
--   Global: exists is Compact forall exists sub mem
-- statement:
--   The Global construction uses the exists is Compact forall exists sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Discrete.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Discrete.lean#L90-L96

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
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

theorem GroundTheory.Global.exists_isCompact_forall_exists_sub_mem :
    ∃ C : Set K∞, IsCompact C ∧ ∀ x : 𝔸[K], ∃ k : K, x - algebraMap K 𝔸[K] k ∈
      C ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by sorry
