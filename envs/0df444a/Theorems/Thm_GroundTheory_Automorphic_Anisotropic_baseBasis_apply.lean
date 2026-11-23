-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_baseBasis_apply
-- name    : GroundTheory.Automorphic.Anisotropic.baseBasis_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:04.396408+00:00
-- url     : https://prove2.me/theorems/adf548cb-d84d-4ecf-9186-30428a086387
-- title:
--   Anisotropic: base Basis apply
-- statement:
--   The Anisotropic construction uses the base Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L25-L26

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

theorem GroundTheory.Automorphic.Anisotropic.baseBasis_apply (k : κ) : baseBasis b R k = 1 ⊗ₜ b k := by sorry
