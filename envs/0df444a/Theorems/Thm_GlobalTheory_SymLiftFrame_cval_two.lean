-- Prove2me | Theorems.Thm_GlobalTheory_SymLiftFrame_cval_two
-- name    : GlobalTheory.SymLiftFrame.cval_two
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:48.062587+00:00
-- url     : https://prove2.me/theorems/f790d4c9-49c8-5e9c-8a3c-cfcc005ce2b7
-- title:
--   Sym Lift Frame: cval two
-- statement:
--   The Sym Lift Frame construction uses the cval two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SymmetricLiftTorsionPointActionOnTheta.lean#L175-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SymmetricLiftTorsionPointActionOnTheta.lean#L175-L184

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymmetricLiftTorsionPointActionOnTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SymLiftFrame
open ThetaFn CubeValues SymmetricSemicharacter AppellHumbertTrivial ReciprocityTheory.ChartRestriction.G.Out
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T} {J : (Sp ℂ ⟶ A.left) → L.ι}
  (hJ : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))

theorem GlobalTheory.SymLiftFrame.cval_two {m : T ⊗ A ⟶ A} {ε : Fin 2 → ℤ}
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ε)) {z w : Fin g → ℂ}
    (h : exAt u p z ≫ m.left = (u.ex w).left) :
    cval α (exAt u p z) J = valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left]
      ![J (u.ex z).left, J (u.ex w).left]) (α.s ![J (u.ex z).left, J (u.ex w).left]).val := by sorry
