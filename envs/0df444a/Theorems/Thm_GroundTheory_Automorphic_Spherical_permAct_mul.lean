-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_permAct_mul
-- name    : GroundTheory.Automorphic.Spherical.permAct_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:14.951801+00:00
-- url     : https://prove2.me/theorems/9ab4d023-b251-4bb3-bc21-d25d23dfe365
-- title:
--   Spherical: perm Act mul
-- statement:
--   The Spherical construction uses the perm Act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L29-L33

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

theorem GroundTheory.Automorphic.Spherical.permAct_mul (σ τ : Equiv.Perm (Fin n)) :
    permAct (σ * τ) = (permAct σ).comp (permAct τ) := by sorry
