-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_polyEmb_rename
-- name    : GroundTheory.Automorphic.Spherical.polyEmb_rename
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:04:18.451799+00:00
-- url     : https://prove2.me/theorems/bc814ce5-cdd8-42f5-a47e-bf861da57d90
-- title:
--   Spherical: poly Emb rename
-- statement:
--   The Spherical construction uses the poly Emb rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SatakeSymmetric.lean#L109-L117

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

theorem GroundTheory.Automorphic.Spherical.polyEmb_rename (σ : Equiv.Perm (Fin n)) (Q : MvPolynomial (Fin n) ℂ) :
    polyEmb n (rename σ Q) = permAct σ (polyEmb n Q) := by sorry
