-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_pullHyp1_restrict_injective
-- name    : GlobalTheory.CechDR.pullHyp1_restrict_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:29:34.1708+00:00
-- url     : https://prove2.me/theorems/cc173454-46d3-4be5-9118-8d503b16b623
-- title:
--   Cech DR: pull Hyp1 restrict injective
-- statement:
--   The Cech DR construction uses the pull Hyp1 restrict injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullHyp1RestrictInjective.lean#L12-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullHyp1RestrictInjective.lean#L12-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullHyp1RestrictInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR

theorem GlobalTheory.CechDR.pullHyp1_restrict_injective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (h1 : Function.Injective (CoefMap.restrict F G).pull1)
    (h0 : ∀ g' : ∀ t, F.obj (G.obj t), (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' = mp F (G.map a) (g' t)) →
      ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ t, g (G.obj t) = g' t)
    (hf : Function.Injective (pullGlob1 (CoefMap.restrict F G))) :
    Function.Injective (pullHyp1 (CoefMap.restrict F G)) := by sorry
