-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_mem_symmetricLaurent
-- name    : GroundTheory.Automorphic.Spherical.mem_symmetricLaurent
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:25.881956+00:00
-- url     : https://prove2.me/theorems/fdd788f3-8f23-5945-9b03-757a0f269b6e
-- title:
--   Spherical: mem symmetric Laurent
-- statement:
--   The Spherical construction uses the mem symmetric Laurent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L62-L64

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

theorem GroundTheory.Automorphic.Spherical.mem_symmetricLaurent {p : LaurentRing n} :
    p ∈ symmetricLaurent n ↔ ∀ σ, permAct σ p = p := by sorry
