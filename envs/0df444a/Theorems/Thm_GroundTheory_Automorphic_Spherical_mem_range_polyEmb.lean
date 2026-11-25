-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_mem_range_polyEmb
-- name    : GroundTheory.Automorphic.Spherical.mem_range_polyEmb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:42.683652+00:00
-- url     : https://prove2.me/theorems/2da26ee1-5a05-4ee7-a038-d4045150e5d7
-- title:
--   Spherical: mem range poly Emb
-- statement:
--   The Spherical construction uses the mem range poly Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L119-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L119-L129

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

theorem GroundTheory.Automorphic.Spherical.mem_range_polyEmb {q : LaurentRing n} (hq : ∀ l ∈ q.coeff.support, ∀ i, 0 ≤ l i) :
    q ∈ (polyEmb n).range := by sorry
