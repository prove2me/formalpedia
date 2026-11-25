-- Prove2me | Theorems.Thm_GlobalTheory_FinOf_finOf_lift
-- name    : GlobalTheory.FinOf.finOf_lift
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:47:12.469839+00:00
-- url     : https://prove2.me/theorems/04ecf4ef-d6c6-45a0-8ecc-860091946af0
-- title:
--   Fin Of: fin Of lift
-- statement:
--   The Fin Of construction uses the fin Of lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinOfLocalAlgebraMap.lean#L112-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinOfLocalAlgebraMap.lean#L112-L128

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FinOf
variable {R₀ : Type} [CommRing R₀]
variable (O : LAlg R₀) {A : Type} [CommRing A] [Algebra (O : Type) A] [Algebra R₀ A]
  [IsScalarTower R₀ (O : Type) A]

theorem GlobalTheory.FinOf.finOf_lift [Module.Finite (O : Type) A] (ε : A) [IsLocalRing (A ⧸ Ideal.span {1 - ε})]
    (S : LAlg R₀) (s : LHom O S) (φ : A →ₐ[R₀] S)
    (hφ : φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s.1) (hε : φ ε = 1) :
    ∃ ψ : LHom ⟨A ⧸ Ideal.span {1 - ε}⟩ S, ψ.comp (finOf_sO O _) = s ∧
      ψ.1.comp (Ideal.Quotient.mkₐ R₀ _) = φ := by sorry
