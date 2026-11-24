-- Prove2me | Theorems.Thm_GlobalTheory_DivisibleHom_exists_eq_pow_of_torsion_comp_eq_one
-- name    : GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:50:46.993799+00:00
-- url     : https://prove2.me/theorems/8f3fb650-2d77-4f4c-a66c-fb8288a85918
-- title:
--   Divisible Hom: exists eq pow of torsion comp eq one
-- statement:
--   The Divisible Hom construction uses the exists eq pow of torsion comp eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsEqPowOfTorsionCompEqOne.lean#L149-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsEqPowOfTorsionCompEqOne.lean#L149-L170

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsEqPowOfTorsionCompEqOne
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
open GlobalTheory GlobalTheory.DivisibleHom
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}

theorem GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV S) (n : ℕ), 1 ≤ n →
      IsFinite (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧ Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧
        Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧
          (IsUnit (n : Γ(S, ⊤)) → Etale (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left)) →
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV S) (B : Over S) [GrpObj B]
      [IsCommMonObj B] (M : ℕ), 1 ≤ M → ∀ u : P.A ⟶ B, IsMonHom u →
        (∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ u = 1) →
          (∃ φ : P.A ⟶ B, IsMonHom φ ∧ u = φ ^ M) ∧ (u ^ M = 1 → u = 1) := by sorry
