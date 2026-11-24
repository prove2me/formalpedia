-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_exists_eq_evalAt
-- name    : GroundTheory.Automorphic.Spherical.exists_eq_evalAt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:41.246784+00:00
-- url     : https://prove2.me/theorems/1d567834-48b0-4bb6-9254-16b1af6c6aa8
-- title:
--   Spherical: exists eq eval At
-- statement:
--   The Spherical construction uses the exists eq eval At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L87-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L87-L107

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
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
open GroundTheory.Automorphic.Spherical
open AddMonoidAlgebra
variable {n : ℕ}

theorem GroundTheory.Automorphic.Spherical.exists_eq_evalAt (ψ : LaurentRing n →ₐ[ℂ] ℂ) : ∃ w : Fin n → ℂˣ, ψ = evalAt w := by sorry
