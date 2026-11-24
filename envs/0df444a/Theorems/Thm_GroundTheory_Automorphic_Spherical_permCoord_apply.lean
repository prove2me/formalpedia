-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_permCoord_apply
-- name    : GroundTheory.Automorphic.Spherical.permCoord_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:58.02663+00:00
-- url     : https://prove2.me/theorems/f25de0b5-9b18-4507-a819-10a2686b994e
-- title:
--   Spherical: perm Coord apply
-- statement:
--   The Spherical construction uses the perm Coord apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L19-L20

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

theorem GroundTheory.Automorphic.Spherical.permCoord_apply (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) : permCoord σ l = l ∘ σ.symm := by sorry
