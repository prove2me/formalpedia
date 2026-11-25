-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_desc_of_flat_of_schemeTheoreticallyDominant_base
-- name    : GlobalTheory.T.exists_desc_of_flat_of_schemeTheoreticallyDominant_base
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:29:34.367165+00:00
-- url     : https://prove2.me/theorems/d2e7e357-9a68-413a-b92a-7c7279931c2a
-- title:
--   T: exists desc of flat of scheme Theoretically Dominant base
-- statement:
--   The T construction uses the exists desc of flat of scheme Theoretically Dominant base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDescOfFlatOfSchemeTheoreticallyDominantBasStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDescOfFlatOfSchemeTheoreticallyDominantBasStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDescOfFlatOfSchemeTheoreticallyDominantBas
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDescOfFlatOfSchemeTheoreticallyDominantBasStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_desc_of_flat_of_schemeTheoreticallyDominant_base : ∀ {S S' U U' X Y Y' YU Y'' : Scheme.{0}} (f : S' ⟶ S) (j : U ⟶ S) (f' : U' ⟶ U) (j' : U' ⟶ S') [Flat f] [Surjective f] [QuasiCompact f] [QuasiCompact j] [IsSchemeTheoreticallyDominant j], IsPullback j' f' f j → ∀ (x : X ⟶ S) [IsSeparated x] (y : Y ⟶ S) [Flat y] (y' : Y' ⟶ S') (π : Y' ⟶ Y), IsPullback π y' y f → ∀ (yU : YU ⟶ U) (ιY : YU ⟶ Y), IsPullback ιY yU y j → ∀ (y'' : Y'' ⟶ U') (c : Y'' ⟶ Y') (cU : Y'' ⟶ YU), IsPullback c y'' y' j' → IsPullback cU y'' yU f' → cU ≫ ιY = c ≫ π → ∀ (h' : Y' ⟶ X) (hU : YU ⟶ X), h' ≫ x = y' ≫ f → c ≫ h' = cU ≫ hU → ∃ h : Y ⟶ X, π ≫ h = h' ∧ ιY ≫ h = hU ∧ h ≫ x = y := by sorry
