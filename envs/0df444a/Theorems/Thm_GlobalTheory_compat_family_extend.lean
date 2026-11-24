-- Prove2me | Theorems.Thm_GlobalTheory_compat_family_extend
-- name    : GlobalTheory.compat_family_extend
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:13:57.515724+00:00
-- url     : https://prove2.me/theorems/01e594b8-597a-4099-917f-e5981c4d9794
-- title:
--   Global Theory: compat family extend
-- statement:
--   The Global Theory construction uses the compat family extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CompatFamilyExtend.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CompatFamilyExtend.lean#L10-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompatFamilyExtend
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
open GlobalTheory

theorem GlobalTheory.compat_family_extend : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) → ∀ g' : ∀ t, F.obj (G.obj t), (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' = mp F (G.map a) (g' t)) → ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ t, g (G.obj t) = g' t := by sorry
