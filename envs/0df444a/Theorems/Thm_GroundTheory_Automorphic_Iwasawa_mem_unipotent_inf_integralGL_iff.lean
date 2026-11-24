-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_unipotent_inf_integralGL_iff
-- name    : GroundTheory.Automorphic.Iwasawa.mem_unipotent_inf_integralGL_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:16:10.050044+00:00
-- url     : https://prove2.me/theorems/2e8d0974-cfa8-4a58-af5c-3698aef16663
-- title:
--   Iwasawa: mem unipotent inf integral GL iff
-- statement:
--   The Iwasawa construction uses the mem unipotent inf integral GL iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L160-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L160-L167

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
variable [ValuativeRel F]

theorem GroundTheory.Automorphic.Iwasawa.mem_unipotent_inf_integralGL_iff {g : GL (Fin n) F} :
    g ∈ unipotent F n ⊓ integralGL F n ↔ g ∈ unipotent F n ∧ ∀ i j, g i j ∈ 𝒪[F] := by sorry
