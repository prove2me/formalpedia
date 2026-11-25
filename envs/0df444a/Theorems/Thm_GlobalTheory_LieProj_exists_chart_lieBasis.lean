-- Prove2me | Theorems.Thm_GlobalTheory_LieProj_exists_chart_lieBasis
-- name    : GlobalTheory.LieProj.exists_chart_lieBasis
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:48:03.634439+00:00
-- url     : https://prove2.me/theorems/510f4483-7e5e-4d09-a13d-aa92862f3613
-- title:
--   Lie Proj: exists chart lie Basis
-- statement:
--   The Lie Proj construction uses the exists chart lie Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteProjectiveOfLocalBasis.lean#L60-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteProjectiveOfLocalBasis.lean#L60-L81

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

theorem GlobalTheory.LieProj.exists_chart_lieBasis : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ),
    SmoothOfRelativeDimension n G.hom → ∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal,
      Nonempty (ReciprocityTheory.ChartRestriction.G.Chart.Chart (ReciprocityTheory.ChartRestriction.G.Chart.Gs G r)) ∧
      ∃ v : Fin n → (epsR (Localization.Away r) ⟶ ReciprocityTheory.ChartRestriction.G.Chart.Gs G r), IsLieBasis v := by sorry
