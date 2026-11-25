-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_permAct_one
-- name    : GroundTheory.Automorphic.Spherical.permAct_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:16.656935+00:00
-- url     : https://prove2.me/theorems/a9375bab-ed85-4732-bc18-50f914a1f394
-- title:
--   Spherical: perm Act one
-- statement:
--   The Spherical construction uses the perm Act one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L35-L38

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

theorem GroundTheory.Automorphic.Spherical.permAct_one : permAct (1 : Equiv.Perm (Fin n)) = AlgHom.id ℂ (LaurentRing n) := by sorry
