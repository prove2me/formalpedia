-- Prove2me | Theorems.Thm_GlobalTheory_T_comma_first_order_cocycle_lift
-- name    : GlobalTheory.T.comma_first_order_cocycle_lift
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:12:07.728974+00:00
-- url     : https://prove2.me/theorems/210cd366-635a-4862-a009-f97e066bac2f
-- title:
--   T: comma first order cocycle lift
-- statement:
--   The T construction uses the comma first order cocycle lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommaFirstOrderCocycleLiftStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommaFirstOrderCocycleLiftStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaFirstOrderCocycleLift
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaFirstOrderCocycleLiftStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.comma_first_order_cocycle_lift : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Injective (CoefMap.restrict F G).pull2 → Function.Surjective (CoefMap.restrict F G).pull1 → (∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) → ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T)) → Function.Surjective (pullGlob1 (CoefMap.restrict F G)) → (∀ (T : C) (x : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u x = 0) → x = 0) → Function.Injective (pullHyp2 (CoefMap.restrict F G)) := by sorry
