-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_polyEmb_X
-- name    : GroundTheory.Automorphic.Spherical.polyEmb_X
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:38:50.074016+00:00
-- url     : https://prove2.me/theorems/5fd8e4e3-d8ea-432a-965f-5a83b82c4f6b
-- title:
--   Spherical: poly Emb X
-- statement:
--   The Spherical construction uses the poly Emb X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L96-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L96-L104

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

theorem GroundTheory.Automorphic.Spherical.polyEmb_X (i : Fin n) : polyEmb n (X i) = monomial (Pi.single i 1) := by sorry
