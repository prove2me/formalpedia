-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_eq_of_forall_mem_adicCompletionIntegers
-- name    : GroundTheory.Global.exists_eq_of_forall_mem_adicCompletionIntegers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:05.784945+00:00
-- url     : https://prove2.me/theorems/12c46951-54ea-46b9-b3ea-8f418002d72b
-- title:
--   Global: exists eq of forall mem adic Completion Integers
-- statement:
--   The Global construction uses the exists eq of forall mem adic Completion Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Discrete.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Discrete.lean#L12-L18

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

theorem GroundTheory.Global.exists_eq_of_forall_mem_adicCompletionIntegers (k : K)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    ∃ z : 𝓞 K, (z : K) = k := by sorry
