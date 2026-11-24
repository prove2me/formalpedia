-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_evalAt_permAct
-- name    : GroundTheory.Automorphic.Spherical.evalAt_permAct
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:16:57.14285+00:00
-- url     : https://prove2.me/theorems/288bb003-f19e-4ad3-85f3-86e672de5d35
-- title:
--   Spherical: eval At perm Act
-- statement:
--   The Spherical construction uses the eval At perm Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L40-L48

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

theorem GroundTheory.Automorphic.Spherical.evalAt_permAct (w : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) (p : LaurentRing n) :
    evalAt w (permAct σ p) = evalAt (w ∘ σ) p := by sorry
