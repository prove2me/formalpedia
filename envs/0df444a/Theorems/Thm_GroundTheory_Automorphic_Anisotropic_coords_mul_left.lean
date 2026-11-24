-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_coords_mul_left
-- name    : GroundTheory.Automorphic.Anisotropic.coords_mul_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:15.604418+00:00
-- url     : https://prove2.me/theorems/e8bb36e6-eacc-404f-9d31-d13d8d3b0c0e
-- title:
--   Anisotropic: coords mul left
-- statement:
--   The Anisotropic construction uses the coords mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L47-L52

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

theorem GroundTheory.Automorphic.Anisotropic.coords_mul_left (a z : R ⊗[K] A) : coords b R (a * z) = coords b R z ᵥ* lmat b R a := by sorry
