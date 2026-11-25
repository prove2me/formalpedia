-- Prove2me | Theorems.Thm_Neutral_B1_equivariant_smul
-- name    : Neutral.B1.equivariant_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:44.005463+00:00
-- url     : https://prove2.me/theorems/cf5aac3f-8f7f-43bb-a1ae-4b0b5c13f030
-- title:
--   B1: equivariant smul
-- statement:
--   The B1 construction uses the equivariant smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Duality.lean#L809-L813
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Duality.lean#L809-L813

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1

theorem Neutral.B1.equivariant_smul {R Γ M : Type*} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (rho : Representation R Γ M) (c : R) :
    ∀ g m, (c • LinearMap.id : M →ₗ[R] M) (rho g m) = rho g ((c • LinearMap.id : M →ₗ[R] M) m) := by sorry
