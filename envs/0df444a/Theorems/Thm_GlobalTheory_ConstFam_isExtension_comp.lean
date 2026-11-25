-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_isExtension_comp
-- name    : GlobalTheory.ConstFam.isExtension_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:07:11.961906+00:00
-- url     : https://prove2.me/theorems/e7462d3a-28d7-4efc-89c8-cff29f735070
-- title:
--   Const Fam: is Extension comp
-- statement:
--   The Const Fam construction uses the is Extension comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/LinearIndependentOfIsExtension.lean#L212-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/LinearIndependentOfIsExtension.lean#L212-L228

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {X X' Y Y' Z : Scheme.{0}}
variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
variable {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}

theorem GlobalTheory.ConstFam.isExtension_comp {k E : Type} [Field k] [Field E] [Algebra k E] {V W W' : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module E W] [AddCommGroup W'] [Module E W'] {a : V →ₛₗ[algebraMap k E] W}
    (ha : IsExtension a) (θ : W →ₗ[E] W') (hθ : Function.Bijective θ) (a' : V →ₛₗ[algebraMap k E] W')
    (e : ∀ v, a' v = θ (a v)) : IsExtension a' := by sorry
