-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_polyEmb_monomial
-- name    : GroundTheory.Automorphic.Spherical.polyEmb_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:04.403438+00:00
-- url     : https://prove2.me/theorems/212c9ad5-a23f-4212-b5fe-ae702f5f49e5
-- title:
--   Spherical: poly Emb monomial
-- statement:
--   The Spherical construction uses the poly Emb monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L92-L94

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

theorem GroundTheory.Automorphic.Spherical.polyEmb_monomial (s : Fin n →₀ ℕ) (c : ℂ) :
    polyEmb n (MvPolynomial.monomial s c) = single (natToInt s) c := by sorry
