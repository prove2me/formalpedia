-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_Segre_ratio_self
-- name    : GlobalTheory.AbLaw.Segre.ratio_self
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:51:37.648301+00:00
-- url     : https://prove2.me/theorems/c5089d6c-9655-4f09-86b6-4ca36798f057
-- title:
--   Segre: ratio self
-- statement:
--   The Segre construction uses the ratio self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L127-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L127-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]
variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}

theorem GlobalTheory.AbLaw.Segre.ratio_self (s : LB.Sec H) (r : Γ(X, nonzeroLocus s))
    (h : ∀ k, rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k) =
      rs X (inf_le_left : nonzeroLocus s ⊓ H.U k ≤ nonzeroLocus s) r *
        rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k)) : r = 1 := by sorry
