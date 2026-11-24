-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_pullHyp2_restrict_injective
-- name    : GlobalTheory.CechDR.pullHyp2_restrict_injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:59:29.831029+00:00
-- url     : https://prove2.me/theorems/e0735364-2cbc-433f-a09e-85ccc5bb667c
-- title:
--   Cech DR: pull Hyp2 restrict injective
-- statement:
--   The Cech DR construction uses the pull Hyp2 restrict injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommaFirstOrderCocycleLift.lean#L14-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommaFirstOrderCocycleLift.lean#L14-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaFirstOrderCocycleLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR

theorem GlobalTheory.CechDR.pullHyp2_restrict_injective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (h2 : Function.Injective (CoefMap.restrict F G).pull2)
    (h1 : Function.Surjective (CoefMap.restrict F G).pull1)
    (hc : ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
        κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) →
      ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R],
        (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) →
        ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T))
    (hf : Function.Surjective (pullGlob1 (CoefMap.restrict F G)))
    (hs : ∀ (T : C) (x : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u x = 0) → x = 0) :
    Function.Injective (pullHyp2 (CoefMap.restrict F G)) := by sorry
