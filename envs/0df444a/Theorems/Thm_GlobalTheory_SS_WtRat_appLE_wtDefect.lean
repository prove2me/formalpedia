-- Prove2me | Theorems.Thm_GlobalTheory_SS_WtRat_appLE_wtDefect
-- name    : GlobalTheory.SS.WtRat.appLE_wtDefect
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:45:27.014808+00:00
-- url     : https://prove2.me/theorems/60d05479-fd4e-4204-ba1c-f777ab85b93d
-- title:
--   Wt Rat: app LE wt Defect
-- statement:
--   The Wt Rat construction uses the app LE wt Defect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusWeightTestGenericPointRationalPoints.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusWeightTestGenericPointRationalPoints.lean#L18-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat

theorem GlobalTheory.SS.WtRat.appLE_wtDefect {Z P G T : Scheme.{0}} (a b : P ⟶ G) (c : P ⟶ T) (V : G.Opens)
    (u : Γ(G, V)) (e : Γ(T, ⊤)) (p : Z ⟶ P) {a' b' : Z ⟶ G} {c' : Z ⟶ T} (ha : p ≫ a = a')
    (hb : p ≫ b = b') (hc : p ≫ c = c') (h : ⊤ ≤ p ⁻¹ᵁ (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V))
    (h₁ : ⊤ ≤ a' ⁻¹ᵁ V) (h₂ : ⊤ ≤ b' ⁻¹ᵁ V) :
    (p.appLE _ ⊤ h).hom (wtDefect a b c V u e) =
      (a'.appLE V ⊤ h₁).hom u - c'.appTop.hom e * (b'.appLE V ⊤ h₂).hom u := by sorry
