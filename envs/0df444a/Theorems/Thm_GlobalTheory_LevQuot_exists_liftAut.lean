-- Prove2me | Theorems.Thm_GlobalTheory_LevQuot_exists_liftAut
-- name    : GlobalTheory.LevQuot.exists_liftAut
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:02:50.801979+00:00
-- url     : https://prove2.me/theorems/96e7c442-f6bd-4cf4-bb06-bc0cb0f27458
-- title:
--   Lev Quot: exists lift Aut
-- statement:
--   The Lev Quot construction uses the exists lift Aut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean#L117-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean#L117-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory GlobalTheory.LevQuot
variable {X Y : Scheme.{0}}

theorem GlobalTheory.LevQuot.exists_liftAut {P Q : Scheme.{0}} {φ : P ⟶ Q} {p : P ⟶ X} {q : Q ⟶ Y} {r : X ⟶ Y} (h : IsPullback φ p q r) :
    ∃ τ : autOver r →* Aut P, ∀ ω, (τ ω).hom ≫ φ = φ ∧ (τ ω).hom ≫ p = p ≫ ω.1.hom := by sorry
