-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_comp_eq_of_antitone
-- name    : GroundTheory.Automorphic.Spherical.comp_eq_of_antitone
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:41.081562+00:00
-- url     : https://prove2.me/theorems/ef0f7ec7-09c1-4c81-bf50-a8e91b1707cd
-- title:
--   Spherical: comp eq of antitone
-- statement:
--   The Spherical construction uses the comp eq of antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L218-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L218-L230

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

theorem GroundTheory.Automorphic.Spherical.comp_eq_of_antitone {ν : Fin n → ℤ} (hν : Antitone ν) (σ : Equiv.Perm (Fin n))
    (hσ : Antitone (ν ∘ σ)) : ν ∘ σ = ν := by sorry
