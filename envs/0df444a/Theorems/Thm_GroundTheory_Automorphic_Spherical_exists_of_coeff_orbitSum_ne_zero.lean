-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_exists_of_coeff_orbitSum_ne_zero
-- name    : GroundTheory.Automorphic.Spherical.exists_of_coeff_orbitSum_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:03.367475+00:00
-- url     : https://prove2.me/theorems/4882c06d-18a9-4e08-9254-c1e8eb75608b
-- title:
--   Spherical: exists of coeff orbit Sum ne zero
-- statement:
--   The Spherical construction uses the exists of coeff orbit Sum ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L205-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L205-L209

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

theorem GroundTheory.Automorphic.Spherical.exists_of_coeff_orbitSum_ne_zero {ν l : Fin n → ℤ} (h : (orbitSum ν).coeff l ≠ 0) :
    ∃ σ : Equiv.Perm (Fin n), ν ∘ σ.symm = l := by sorry
