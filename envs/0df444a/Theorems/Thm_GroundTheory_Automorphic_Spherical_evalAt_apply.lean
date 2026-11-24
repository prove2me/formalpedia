-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_evalAt_apply
-- name    : GroundTheory.Automorphic.Spherical.evalAt_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:21:45.176589+00:00
-- url     : https://prove2.me/theorems/de8ecf22-34a1-4189-aa87-a86a27ea701e
-- title:
--   Spherical: eval At apply
-- statement:
--   The Spherical construction uses the eval At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L51-L54

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

theorem GroundTheory.Automorphic.Spherical.evalAt_apply (w : Fin n → ℂˣ) (p : LaurentRing n) :
    evalAt w p = p.coeff.sum fun l c => c * monomialChar l w := by sorry
