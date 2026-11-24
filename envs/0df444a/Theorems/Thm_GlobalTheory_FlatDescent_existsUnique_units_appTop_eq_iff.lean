-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_existsUnique_units_appTop_eq_iff
-- name    : GlobalTheory.FlatDescent.existsUnique_units_appTop_eq_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:32:09.860686+00:00
-- url     : https://prove2.me/theorems/478103ea-121c-4e40-bc23-a06a8fbe1bcc
-- title:
--   Flat Descent: exists Unique units app Top eq iff
-- statement:
--   The Flat Descent construction uses the exists Unique units app Top eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L66-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}

theorem GlobalTheory.FlatDescent.existsUnique_units_appTop_eq_iff (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)ˣ) :
    (∃! a : Γ(X, ⊤)ˣ, Units.map p.appTop.hom.toMonoidHom a = s) ↔
      Units.map f.appTop.hom.toMonoidHom s = Units.map g.appTop.hom.toMonoidHom s := by sorry
