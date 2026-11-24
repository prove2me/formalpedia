-- Prove2me | Theorems.Thm_GlobalTheory_ExtendLineBundle_isGen_of_equations
-- name    : GlobalTheory.ExtendLineBundle.isGen_of_equations
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:18:01.120875+00:00
-- url     : https://prove2.me/theorems/ffd57b29-a6dd-401a-b1a6-c090e709d06a
-- title:
--   Extend Line Bundle: is Gen of equations
-- statement:
--   The Extend Line Bundle construction uses the is Gen of equations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L337-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L337-L359

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
variable (j : Y ⟶ X) [IsOpenImmersion j]

theorem GlobalTheory.ExtendLineBundle.isGen_of_equations (M N : LB Y) (a : M.ι → X.functionFieldˣ) (b : N.ι → X.functionFieldˣ)
    (ha : ∀ i k, genericPoint X ∈ j ''ᵁ M.U i → genericPoint X ∈ j ''ᵁ M.U k →
      imageVal j _ (M.g i k) = a i / a k)
    (hb : ∀ i k, genericPoint X ∈ j ''ᵁ N.U i → genericPoint X ∈ j ''ᵁ N.U k →
      imageVal j _ (N.g i k) = b i / b k)
    (s : ∀ p : M.ι × N.ι, Γ(Y, M.U p.1 ⊓ N.U p.2)ˣ)
    (hs : ∀ p, genericPoint X ∈ j ''ᵁ (M.U p.1 ⊓ N.U p.2) → imageVal j _ (s p) = a p.1 / b p.2) :
    LB.Gen.IsGen (⟨s⟩ : LB.Iso N M) := by sorry
