-- Prove2me | Theorems.Thm_GlobalTheory_T_locally_trivial_unit_cocycle_faithfully_flat
-- name    : GlobalTheory.T.locally_trivial_unit_cocycle_faithfully_flat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:10.908871+00:00
-- url     : https://prove2.me/theorems/d7318db6-6afe-4814-a9fb-944c635b62e5
-- title:
--   T: locally trivial unit cocycle faithfully flat
-- statement:
--   The T construction uses the locally trivial unit cocycle faithfully flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyTrivialUnitCocycleFaithfullyFlatStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyTrivialUnitCocycleFaithfullyFlatStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.locally_trivial_unit_cocycle_faithfully_flat : ∀ (R B C D : CommRingCat.{0}) (f : R ⟶ B) (j₁ j₂ : B ⟶ C) (d₁₂ d₂₃ d₁₃ : C ⟶ D), IsPushout f f j₁ j₂ → IsPushout j₂ j₁ d₁₂ d₂₃ → j₁ ≫ d₁₃ = j₁ ≫ d₁₂ → j₂ ≫ d₁₃ = j₂ ≫ d₂₃ → f.hom.FaithfullyFlat → ∀ c : Cˣ, d₁₃.hom (c : C) = d₁₂.hom (c : C) * d₂₃.hom (c : C) → ∀ P : Ideal R, P.IsPrime → ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = f.hom s ∧ j₂.hom x = (c : C) * j₁.hom x := by sorry
