-- Prove2me | Theorems.Thm_GlobalTheory_VolFin_tr_linComb
-- name    : GlobalTheory.VolFin.tr_linComb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:46.540933+00:00
-- url     : https://prove2.me/theorems/dfa61166-a017-4852-b40f-d6b0324aa109
-- title:
--   Vol Fin: tr lin Comb
-- statement:
--   The Vol Fin construction uses the tr lin Comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LineBundleGlobalSectionsFunctionFieldIff.lean#L175-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LineBundleGlobalSectionsFunctionFieldIff.lean#L175-L183

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
omit [IsIntegral Y]

theorem GlobalTheory.VolFin.tr_linComb (N : LB Y) (ψ : X ⟶ Y) (ε : ℤ) (e : ℕ) (hε : ε = e) (J J' : PUnit → N.ι)
    (h) (h') (h'') :
    tr (LB.LinComb N (K := PUnit) (fun _ => ψ) (fun _ => ε)) J J' h h' =
      gen (ψ ⁻¹ᵁ (N.U (J ⟨⟩) ⊓ N.U (J' ⟨⟩))) h'' ((ψ.app _).hom (N.g _ _).val) ^ e := by sorry
