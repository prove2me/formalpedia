-- Prove2me | Theorems.Thm_GlobalTheory_ideal_map_colon_eq_of_flat
-- name    : GlobalTheory.ideal_map_colon_eq_of_flat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:11.597604+00:00
-- url     : https://prove2.me/theorems/9e3e8c23-1339-45b4-8937-5daebe6a81e1
-- title:
--   Global Theory: ideal map colon eq of flat
-- statement:
--   The Global Theory construction uses the ideal map colon eq of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FlatMapColonIdeal.lean#L14-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FlatMapColonIdeal.lean#L14-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatMapColonIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.ideal_map_colon_eq_of_flat : ∀ {A R : Type} [CommRing A] [IsNoetherianRing A] [CommRing R]
    (φ : A →+* R), φ.Flat → ∀ I J : Ideal A, (I.colon J).map φ = (I.map φ).colon (J.map φ) := by sorry
