-- Prove2me | Theorems.Thm_GlobalTheory_VolFin_lineBundle_global_sections_functionField_iff
-- name    : GlobalTheory.VolFin.lineBundle_global_sections_functionField_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:51:19.403134+00:00
-- url     : https://prove2.me/theorems/5179ad5a-7228-466e-8816-7e63691a59cf
-- title:
--   Vol Fin: line Bundle global sections function Field iff
-- statement:
--   The Vol Fin construction uses the line Bundle global sections function Field iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LineBundleGlobalSectionsFunctionFieldIff.lean#L114-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LineBundleGlobalSectionsFunctionFieldIff.lean#L114-L160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleGlobalSectionsFunctionFieldIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)
noncomputable section
open GlobalTheory GlobalTheory.VolFin
variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem GlobalTheory.VolFin.lineBundle_global_sections_functionField_iff [Algebra K X.functionField] (p : X ⟶ Sp K)
    (halg : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn p ⊤ a))
    {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (V : Submodule K X.functionField)
    (hV : ∀ f, f ∈ V ↔ ∀ i, ∃ a, gen (W i) (hη i) a = f * tr N (c i) j₀ (hW i (hη i)) h₀) (r : ℕ) :
    SectionsHaveFiniteDimension p N r ↔ Module.Finite K V ∧ Module.finrank K V = r := by sorry
