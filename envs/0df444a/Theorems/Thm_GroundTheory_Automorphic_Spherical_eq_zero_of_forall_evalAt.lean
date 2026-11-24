-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_eq_zero_of_forall_evalAt
-- name    : GroundTheory.Automorphic.Spherical.eq_zero_of_forall_evalAt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:52.474861+00:00
-- url     : https://prove2.me/theorems/0ade13ed-bbd4-4420-b4c6-cd8449836051
-- title:
--   Spherical: eq zero of forall eval At
-- statement:
--   The Spherical construction uses the eq zero of forall eval At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L69-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L69-L82

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

theorem GroundTheory.Automorphic.Spherical.eq_zero_of_forall_evalAt {p : LaurentRing n} (h : ∀ w, evalAt w p = 0) : p = 0 := by sorry
