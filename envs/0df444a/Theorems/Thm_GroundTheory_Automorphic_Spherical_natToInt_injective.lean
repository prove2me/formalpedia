-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_natToInt_injective
-- name    : GroundTheory.Automorphic.Spherical.natToInt_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:00.421154+00:00
-- url     : https://prove2.me/theorems/a809a365-5b0f-4f9f-a497-8cd3253d5c26
-- title:
--   Spherical: nat To Int injective
-- statement:
--   The Spherical construction uses the nat To Int injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L83-L85

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

theorem GroundTheory.Automorphic.Spherical.natToInt_injective : Function.Injective (natToInt (n := n)) := by sorry
