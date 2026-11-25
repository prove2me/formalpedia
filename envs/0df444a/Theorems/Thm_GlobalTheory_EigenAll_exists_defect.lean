-- Prove2me | Theorems.Thm_GlobalTheory_EigenAll_exists_defect
-- name    : GlobalTheory.EigenAll.exists_defect
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:48:27.384798+00:00
-- url     : https://prove2.me/theorems/181f3711-ba34-48cc-a880-97b3923ecf3e
-- title:
--   Eigen All: exists defect
-- statement:
--   The Eigen All construction uses the exists defect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EigenEquationOfForallGeometricPoint.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/EigenEquationOfForallGeometricPoint.lean#L22-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SectionEqZeroOfForallGeometricPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EigenEquationOfForallGeometricPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.EigenAll

theorem GlobalTheory.EigenAll.exists_defect {Y G H : Scheme.{0}} (m s : Y ⟶ G) (p : Y ⟶ H) (V : G.Opens) (t : Γ(G, V))
    (u : Γ(H, ⊤)) : ∃ f : Γ(Y, m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V), ∀ (Z : Scheme.{0}) (g : Z ⟶ Y) (z : Z),
      g z ∈ m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V → gs g z (m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V) f =
        gs (g ≫ m) z V t - gs (g ≫ p) z ⊤ u * gs (g ≫ s) z V t := by sorry
