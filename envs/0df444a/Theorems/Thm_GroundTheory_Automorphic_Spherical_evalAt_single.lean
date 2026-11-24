-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_evalAt_single
-- name    : GroundTheory.Automorphic.Spherical.evalAt_single
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:12:54.111347+00:00
-- url     : https://prove2.me/theorems/8674f284-f04a-412c-a909-f292eae70209
-- title:
--   Spherical: eval At single
-- statement:
--   The Spherical construction uses the eval At single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L46-L49

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

theorem GroundTheory.Automorphic.Spherical.evalAt_single (w : Fin n → ℂˣ) (l : Fin n → ℤ) (c : ℂ) :
    evalAt w (single l c) = c * monomialChar l w := by sorry
