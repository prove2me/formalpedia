-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_map_det_krylov_C_X
-- name    : GroundTheory.Automorphic.map_det_krylov_C_X
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:45.015521+00:00
-- url     : https://prove2.me/theorems/392ef80b-0948-435f-abd0-98bb7a61ddf1
-- title:
--   Automorphic: map det krylov C X
-- statement:
--   The Automorphic construction uses the map det krylov C X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L77-L81

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Polynomial Module Matrix
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
variable {E : Type*} [Field E]

theorem GroundTheory.Automorphic.map_det_krylov_C_X {T : Type*} [CommRing T] (M : Matrix (Fin n) (Fin n) E)
    (ψ : MvPolynomial (Fin n) E →+* T) :
    ψ (krylov (M.map MvPolynomial.C) (fun i => MvPolynomial.X i)).det =
      (krylov ((M.map MvPolynomial.C).map ψ) (ψ ∘ fun i => MvPolynomial.X i)).det := by sorry
