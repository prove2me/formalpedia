-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmat_injective
-- name    : GroundTheory.Automorphic.Anisotropic.rmat_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:25.653113+00:00
-- url     : https://prove2.me/theorems/27fcebdc-7709-4b62-953e-4efc01feff0c
-- title:
--   Anisotropic: rmat injective
-- statement:
--   The Anisotropic construction uses the rmat injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L78-L84

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K : Type*} [Field K] {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {A : Type*} [Ring A] [Algebra K A] (b : Module.Basis κ K A)
variable (R : Type*) [CommRing R] [Algebra K R]

theorem GroundTheory.Automorphic.Anisotropic.rmat_injective : Function.Injective (rmat b R) := by sorry
