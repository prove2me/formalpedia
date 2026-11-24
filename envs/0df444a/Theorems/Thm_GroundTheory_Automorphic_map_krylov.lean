-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_map_krylov
-- name    : GroundTheory.Automorphic.map_krylov
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:03.721806+00:00
-- url     : https://prove2.me/theorems/061abfb4-25e9-402e-b4bc-eacb1398fe89
-- title:
--   Automorphic: map krylov
-- statement:
--   The Automorphic construction uses the map krylov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L67-L73

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

theorem GroundTheory.Automorphic.map_krylov (φ : R →+* S) (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    (krylov M v).map φ = krylov (M.map φ) (φ ∘ v) := by sorry
