-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_permAct_single
-- name    : GroundTheory.Automorphic.Spherical.permAct_single
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:12.723799+00:00
-- url     : https://prove2.me/theorems/024517e4-0755-4353-930c-3dccf6f7d52b
-- title:
--   Spherical: perm Act single
-- statement:
--   The Spherical construction uses the perm Act single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L25-L27

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
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
open AddMonoidAlgebra MvPolynomial
open GroundTheory.Automorphic.Spherical
variable {n : ℕ}

theorem GroundTheory.Automorphic.Spherical.permAct_single (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) (c : ℂ) :
    permAct σ (single l c) = single (l ∘ σ.symm) c := by sorry
