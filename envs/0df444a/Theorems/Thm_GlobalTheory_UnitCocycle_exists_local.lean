-- Prove2me | Theorems.Thm_GlobalTheory_UnitCocycle_exists_local
-- name    : GlobalTheory.UnitCocycle.exists_local
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:25:23.15636+00:00
-- url     : https://prove2.me/theorems/3b31e371-48d0-46ad-a9f4-dbbc51139bb3
-- title:
--   Unit Cocycle: exists local
-- statement:
--   The Unit Cocycle construction uses the exists local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyTrivialUnitCocycleFaithfullyFlat.lean#L110-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyTrivialUnitCocycleFaithfullyFlat.lean#L110-L161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
open GlobalTheory
open GlobalTheory.UnitCocycle

theorem GlobalTheory.UnitCocycle.exists_local (R B C D : CommRingCat.{0}) (f : R ⟶ B) (j₁ j₂ : B ⟶ C) (d₁₂ d₂₃ d₁₃ : C ⟶ D)
    (hC : IsPushout f f j₁ j₂) (hD : IsPushout j₂ j₁ d₁₂ d₂₃) (h₁ : j₁ ≫ d₁₃ = j₁ ≫ d₁₂)
    (h₂ : j₂ ≫ d₁₃ = j₂ ≫ d₂₃) (hf : f.hom.FaithfullyFlat) (c : Cˣ)
    (hc : d₁₃.hom (c : C) = d₁₂.hom (c : C) * d₂₃.hom (c : C)) (P : Ideal R) (hP : P.IsPrime) :
    ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = f.hom s ∧ j₂.hom x = (c : C) * j₁.hom x := by sorry
