-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_square_generator_through_squareIso
-- name    : GlobalTheory.T.exists_square_generator_through_squareIso
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:26.185921+00:00
-- url     : https://prove2.me/theorems/52ce3632-4941-4861-b694-6792273c2604
-- title:
--   T: exists square generator through square Iso
-- statement:
--   The T construction uses the exists square generator through square Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSquareGeneratorThroughSquareIsoStatement.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsSquareGeneratorThroughSquareIsoStatement.lean#L10-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSquareGeneratorThroughSquareIso
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSquareGeneratorThroughSquareIsoStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_square_generator_through_squareIso : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}, L.IsLB → L'.IsLB →
    ∀ (w : LB.Iso (LB.LinComb L' (K := Fin 1) (fun _ => 𝟙 X') (fun _ => 2))
      ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).pull F)), w.IsGen →
    ∀ {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∃ W : ∀ (Z : Scheme.{0}) (z : Z), (K → (Z ⟶ X')) → ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) →
          (Z.presheaf.stalk z)ˣ,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι),
          Good L z J → Good L' z J' → val t r z J = W Z z (fun k => r ≫ φ' k) J J' * val a r z J' ^ 2 := by sorry
