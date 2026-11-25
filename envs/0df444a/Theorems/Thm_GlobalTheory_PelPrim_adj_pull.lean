-- Prove2me | Theorems.Thm_GlobalTheory_PelPrim_adj_pull
-- name    : GlobalTheory.PelPrim.adj_pull
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:25:16.225814+00:00
-- url     : https://prove2.me/theorems/f16d8da2-f589-4a41-b016-1064ece8a07b
-- title:
--   Pel Prim: adj pull
-- statement:
--   The Pel Prim construction uses the adj pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PelObjectClassPrimAndIsoClosed.lean#L69-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PelObjectClassPrimAndIsoClosed.lean#L69-L78

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

theorem GlobalTheory.PelPrim.adj_pull (ψ : A ⟶ G) [IsMonHom ψ] {L : LB A.left} {M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull ψ.left)) {u v : A ⟶ A} {u₀ v₀ : G ⟶ G} (hu : u ≫ ψ = ψ ≫ u₀) (hv : v ≫ ψ = ψ ≫ v₀)
    (H : LBIso (cubeLB G ![fst G G ≫ u₀, snd G G] M) (cubeLB G ![fst G G, snd G G ≫ v₀] M)) :
    LBIso (cubeLB A ![fst A A ≫ u, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ v] L) := by sorry
