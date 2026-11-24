-- Prove2me | Theorems.Thm_GlobalTheory_expands_linear
-- name    : GlobalTheory.expands_linear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:23:58.974338+00:00
-- url     : https://prove2.me/theorems/2c87b556-bd6a-4047-ab74-637a62dd3c5b
-- title:
--   Global Theory: expands linear
-- statement:
--   The Global Theory construction uses the expands linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ScalCompSpecMap.lean#L84-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ScalCompSpecMap.lean#L84-L109

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ScalCompSpecMap
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ExpandsLinear

theorem GlobalTheory.expands_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (n : ℕ) (b : Fin n → U.SecK k) (F : Fin n → Fam D.toPre (FractionRing R) k) (c : Fin n → FractionRing R) (s : U.SecK k), (∀ i, U.Expands k (b i) (F i)) → (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) → U.Expands k s (∑ i, c i • F i) := by sorry
