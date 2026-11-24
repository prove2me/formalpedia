-- Prove2me | Theorems.Thm_GlobalTheory_exists_desc_of_flat_of_schemeTheoreticallyDominant
-- name    : GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:24.523554+00:00
-- url     : https://prove2.me/theorems/6bf0dbe3-0ee0-4cd2-a713-685500145c77
-- title:
--   Global Theory: exists desc of flat of scheme Theoretically Dominant
-- statement:
--   The Global Theory construction uses the exists desc of flat of scheme Theoretically Dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDescOfFlatOfSchemeTheoreticallyDominantBas.lean#L7-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDescOfFlatOfSchemeTheoreticallyDominantBas.lean#L7-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDescOfFlatOfSchemeTheoreticallyDominantBas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory

theorem GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant :
    ∀ {S S' U U' X Y Y' YU Y'' : Scheme.{0}} (f : S' ⟶ S) (j : U ⟶ S) (f' : U' ⟶ U) (j' : U' ⟶ S')
      [Flat f] [Surjective f] [QuasiCompact f] [QuasiCompact j] [IsSchemeTheoreticallyDominant j],
      IsPullback j' f' f j → ∀ (x : X ⟶ S) [IsSeparated x] (y : Y ⟶ S) [Flat y] (y' : Y' ⟶ S')
      (π : Y' ⟶ Y), IsPullback π y' y f → ∀ (yU : YU ⟶ U) (ιY : YU ⟶ Y), IsPullback ιY yU y j →
      ∀ (y'' : Y'' ⟶ U') (c : Y'' ⟶ Y') (cU : Y'' ⟶ YU), IsPullback c y'' y' j' →
      IsPullback cU y'' yU f' → cU ≫ ιY = c ≫ π → ∀ (h' : Y' ⟶ X) (hU : YU ⟶ X),
      h' ≫ x = y' ≫ f → c ≫ h' = cU ≫ hU → ∃ h : Y ⟶ X, π ≫ h = h' ∧ ιY ≫ h = hU ∧ h ≫ x = y := by sorry
