-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_coeff_orbitSum
-- name    : GroundTheory.Automorphic.Spherical.coeff_orbitSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:59.050394+00:00
-- url     : https://prove2.me/theorems/422c6b5d-8150-4803-8aff-9ea335554dd0
-- title:
--   Spherical: coeff orbit Sum
-- statement:
--   The Spherical construction uses the coeff orbit Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L195-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L195-L203

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

theorem GroundTheory.Automorphic.Spherical.coeff_orbitSum (ν l : Fin n → ℤ) :
    (orbitSum ν).coeff l = ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      ν ∘ σ.symm = l).card : ℂ) := by sorry
