-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_unipotent
-- name    : GroundTheory.Automorphic.Iwasawa.mem_unipotent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:48.848313+00:00
-- url     : https://prove2.me/theorems/803e6582-dbfa-48bb-aa46-ce4a19d6b604
-- title:
--   Iwasawa: mem unipotent
-- statement:
--   The Iwasawa construction uses the mem unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L82-L84

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)

theorem GroundTheory.Automorphic.Iwasawa.mem_unipotent {g : GL (Fin n) F} :
    g ∈ unipotent F n ↔ (g : Matrix (Fin n) (Fin n) F).IsUpperTriangular ∧ ∀ i, g i i = 1 := by sorry
