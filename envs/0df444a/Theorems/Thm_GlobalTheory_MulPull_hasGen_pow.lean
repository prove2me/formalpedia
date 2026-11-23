-- Prove2me | Theorems.Thm_GlobalTheory_MulPull_hasGen_pow
-- name    : GlobalTheory.MulPull.hasGen_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:39.73568+00:00
-- url     : https://prove2.me/theorems/4b07dece-4ab4-4f92-80ae-1a9d7f3d59f2
-- title:
--   Mul Pull: has Gen pow
-- statement:
--   The Mul Pull construction uses the has Gen pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MulPullOfCubeOfSymm.lean#L48-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MulPullOfCubeOfSymm.lean#L48-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulPullOfCubeOfSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem GlobalTheory.MulPull.hasGen_pow (hL : L.IsLB) (hcube : HasGen L (thφ A (x3 A)) thε) {T : Over S} (x : T ⟶ A)
    (hone : HasGen L (K := Fin 1) ![(1 : T ⟶ A).left] ![1])
    (hsym : HasGen L (K := Fin 2) ![x.left, (x⁻¹).left] ![1, -1]) (n : ℕ) :
    HasGen L (K := Fin 2) ![x.left, (x ^ n).left] ![(n : ℤ) ^ 2, -1] := by sorry
