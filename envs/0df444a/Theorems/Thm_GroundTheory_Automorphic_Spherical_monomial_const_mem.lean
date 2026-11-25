-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_monomial_const_mem
-- name    : GroundTheory.Automorphic.Spherical.monomial_const_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:01.599347+00:00
-- url     : https://prove2.me/theorems/753a6dfb-8cd6-4cd2-a9e3-bc7c12d20d09
-- title:
--   Spherical: monomial const mem
-- statement:
--   The Spherical construction uses the monomial const mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L66-L69

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

theorem GroundTheory.Automorphic.Spherical.monomial_const_mem (c : ℤ) : monomial (fun _ : Fin n => c) ∈ symmetricLaurent n := by sorry
