-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_natToInt_apply
-- name    : GroundTheory.Automorphic.Spherical.natToInt_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:02.63813+00:00
-- url     : https://prove2.me/theorems/4b29c398-1e1f-4563-ac70-5a3bfccce693
-- title:
--   Spherical: nat To Int apply
-- statement:
--   The Spherical construction uses the nat To Int apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L80-L81

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

theorem GroundTheory.Automorphic.Spherical.natToInt_apply (s : Fin n →₀ ℕ) (i : Fin n) : natToInt s i = s i := by sorry
