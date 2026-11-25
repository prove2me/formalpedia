-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_eq_of_forall_evalAt
-- name    : GroundTheory.Automorphic.Spherical.eq_of_forall_evalAt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:21:27.419249+00:00
-- url     : https://prove2.me/theorems/77d02eaa-d650-48a2-b373-89117559301a
-- title:
--   Spherical: eq of forall eval At
-- statement:
--   The Spherical construction uses the eq of forall eval At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L84-L85

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

theorem GroundTheory.Automorphic.Spherical.eq_of_forall_evalAt {p q : LaurentRing n} (h : ∀ w, evalAt w p = evalAt w q) : p = q := by sorry
