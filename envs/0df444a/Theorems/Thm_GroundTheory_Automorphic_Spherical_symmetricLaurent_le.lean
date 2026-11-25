-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_symmetricLaurent_le
-- name    : GroundTheory.Automorphic.Spherical.symmetricLaurent_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:36:26.998126+00:00
-- url     : https://prove2.me/theorems/e7d87a4e-5f6e-4edb-bad8-1cd2dc609b88
-- title:
--   Spherical: symmetric Laurent le
-- statement:
--   The Spherical construction uses the symmetric Laurent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L131-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L131-L184

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

theorem GroundTheory.Automorphic.Spherical.symmetricLaurent_le {A : Subalgebra ℂ (LaurentRing n)}
    (he : ∀ k, polyEmb n (esymm (Fin n) ℂ k) ∈ A) (hinv : monomial (fun _ => (-1 : ℤ)) ∈ A) :
    symmetricLaurent n ≤ A := by sorry
