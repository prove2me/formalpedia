-- Prove2me | Theorems.Thm_GlobalTheory_GeneratorLaw_gm_of_nv
-- name    : GlobalTheory.GeneratorLaw.gm_of_nv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:38:46.160544+00:00
-- url     : https://prove2.me/theorems/8ebba8d7-5e6d-58e5-a4e5-838de3216d9e
-- title:
--   Generator Law: gm of nv
-- statement:
--   The Generator Law construction uses the gm of nv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGrpObjSplitExtensionOfGenerators.lean#L429-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGrpObjSplitExtensionOfGenerators.lean#L429-L438

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGrpObjSplitExtensionOfGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GeneratorLaw
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {κ : Type} {O : κ → RigLB B} {G : Over S} [GrpObj G]
  {q : G ⟶ B} {u : ∀ k (i : (O k).L.ι), Γ(G.left, q.left ⁻¹ᵁ (O k).L.U i)ˣ}
omit [GrpObj G]

theorem GlobalTheory.GeneratorLaw.gm_of_nv {W : Over S} {g g' : W ⟶ G} {c : PV O W} (h₁ : g' ≫ q = g ≫ q)
    (h₂ : nv O q u g' = c * nv O q u g) (k : κ) (z : W.left) (i : (O k).L.ι)
    (hi : q.left (g.left z) ∈ (O k).L.U i) : ∃ J, gm g'.left z (q.left ⁻¹ᵁ (O k).L.U i) (u k i) =
      c k z J * gm g.left z (q.left ⁻¹ᵁ (O k).L.U i) (u k i) := by sorry
