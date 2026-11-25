-- Prove2me | Theorems.Thm_GlobalTheory_FinOf_finOf_unram
-- name    : GlobalTheory.FinOf.finOf_unram
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:43:20.667736+00:00
-- url     : https://prove2.me/theorems/9b79bee5-1b72-5118-8376-21d2baa27b90
-- title:
--   Fin Of: fin Of unram
-- statement:
--   The Fin Of construction uses the fin Of unram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinOfLocalAlgebraMap.lean#L206-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinOfLocalAlgebraMap.lean#L206-L229

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

theorem GlobalTheory.FinOf.finOf_unram (B : BX R₀) (p : ℕ) (hp : p ≠ 0)
    (pt : ∀ S : LAlg R₀, (A →ₐ[R₀] S) → B.G S)
    (pt_nat : ∀ {S S' : LAlg R₀} (f : LHom S S') (φ : A →ₐ[R₀] S),
      B.map f (pt S φ) = pt S' (f.1.comp φ))
    (pt_p : ∀ S φ, p • pt S φ = 0)
    (pt_univ : ∀ (S : LAlg R₀) (s : O →ₐ[R₀] S) (z : B.G S), p • z = 0 →
      ∃! φ : A →ₐ[R₀] S, φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s ∧ pt S φ = z)
    (C : Type) [Field C] [CharZero C] [Algebra (O : Type) C] [Algebra R₀ C]
    [IsScalarTower R₀ (O : Type) C] (φ φ' : A →ₐ[(O : Type)] DualNumber C)
    (h : ∀ a, (φ a).fst = (φ' a).fst) : φ = φ' := by sorry
