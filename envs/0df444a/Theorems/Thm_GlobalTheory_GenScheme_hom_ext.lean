-- Prove2me | Theorems.Thm_GlobalTheory_GenScheme_hom_ext
-- name    : GlobalTheory.GenScheme.hom_ext
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:28:15.166304+00:00
-- url     : https://prove2.me/theorems/380fe881-c448-5e40-9011-4dc2369afaa3
-- title:
--   Gen Scheme: hom ext
-- statement:
--   The Gen Scheme construction uses the hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean#L131-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean#L131-L143

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory
open GlobalTheory.GenScheme
variable {B : Scheme.{0}} {κ : Type} {N : κ → LB B} {G : Scheme.{0}} {q : G ⟶ B}
  {u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ}

theorem GlobalTheory.GenScheme.hom_ext (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u) {Z : Scheme.{0}}
    (j : ∀ k, (N k).ι) (g g' : Z ⟶ G) (hg : g' ≫ q = g ≫ q)
    (hj : ∀ k, ⊤ ≤ g ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)) (hj' : ∀ k, ⊤ ≤ g' ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k))
    (h : ∀ k, pb g' (q ⁻¹ᵁ (N k).U (j k)) ⊤ (hj' k) (u k (j k)) =
      pb g (q ⁻¹ᵁ (N k).U (j k)) ⊤ (hj k) (u k (j k))) : g' = g := by sorry
