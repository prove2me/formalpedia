-- Prove2me | Theorems.Thm_GlobalTheory_GenScheme_exists_isPullback
-- name    : GlobalTheory.GenScheme.exists_isPullback
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:33:24.492737+00:00
-- url     : https://prove2.me/theorems/e28446c8-87d6-4a7a-a224-cad6bce3dbbb
-- title:
--   Gen Scheme: exists is Pullback
-- statement:
--   The Gen Scheme construction uses the exists is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean#L161-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/GeneratorSchemeProperties.lean#L161-L200

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Theorems.Thm_GlobalTheory_Diag_exists_isPullback

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
open SplitTorus

theorem GlobalTheory.GenScheme.exists_isPullback (hN : ∀ k, (N k).IsLB) (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u)
    {V : Scheme.{0}} (v : V ⟶ B) (j : ∀ k, (N k).ι) (hj : ∀ k, ⊤ ≤ v ⁻¹ᵁ (N k).U (j k)) :
    ∃ p : (splitTorus V (κ →₀ ℤ)).left ⟶ G, IsPullback p (splitTorus V (κ →₀ ℤ)).hom q v := by sorry
