-- Prove2me | Theorems.Thm_GlobalTheory_LieProj_finite_projective_of_localBasis
-- name    : GlobalTheory.LieProj.finite_projective_of_localBasis
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:50:43.990067+00:00
-- url     : https://prove2.me/theorems/c2f6f5a8-fd13-5475-889b-786dffb7947a
-- title:
--   Lie Proj: finite projective of local Basis
-- statement:
--   The Lie Proj construction uses the finite projective of local Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteProjectiveOfLocalBasis.lean#L19-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteProjectiveOfLocalBasis.lean#L19-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnivChartOfStandardSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushRProdPtsResP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteProjectiveOfLocalBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LieProj

theorem GlobalTheory.LieProj.finite_projective_of_localBasis : ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ),
    (∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal,
      Nonempty (Module.Basis (Fin n) (Localization.Away r) (LocalizedModule (Submonoid.powers r) M))) →
    Module.Finite R M ∧ Module.Projective R M ∧ ∀ p, Module.rankAtStalk (R := R) M p = n := by sorry
