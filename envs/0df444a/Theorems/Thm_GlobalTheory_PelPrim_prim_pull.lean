-- Prove2me | Theorems.Thm_GlobalTheory_PelPrim_prim_pull
-- name    : GlobalTheory.PelPrim.prim_pull
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:25:04.571059+00:00
-- url     : https://prove2.me/theorems/3c608e7f-2669-5920-ace5-217df235eb6f
-- title:
--   Pel Prim: prim pull
-- statement:
--   The Pel Prim construction uses the prim pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PelObjectClassPrimAndIsoClosed.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PelObjectClassPrimAndIsoClosed.lean#L80-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PelObjectClassPrimAndIsoClosed
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
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.PelPrim
variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

theorem GlobalTheory.PelPrim.prim_pull (ψ : A ⟶ G) [IsMonHom ψ] {L : LB A.left} {M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull ψ.left)) {u : A ⟶ A} {u₀ : G ⟶ G} (hu : u ≫ ψ = ψ ≫ u₀)
    (H : LBIso M (cubeLB G ![𝟙 G, u₀] M)) : LBIso L (cubeLB A ![𝟙 A, u] L) := by sorry
