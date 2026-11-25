-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LieModel_isGrNorm_iff_formGramAt
-- name    : GlobalTheory.CompanionTheory.Ar.LieModel.isGrNorm_iff_formGramAt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:00:57.201411+00:00
-- url     : https://prove2.me/theorems/83c7ea7c-359f-4809-8417-c8de3cc4267a
-- title:
--   Lie Model: is Gr Norm iff form Gram At
-- statement:
--   The Lie Model construction uses the is Gr Norm iff form Gram At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/HodgeIPIffHodgeFormConj.lean#L148-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/HodgeIPIffHodgeFormConj.lean#L148-L158

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable {M : LieModel G ξ E} {L : LB G.left} {V : Lat ξ E} {r : ℕ} {b₀ : Fin r → E} {i : Fin r}
  {z : Spec (CommRingCat.of ℂ) ⟶ X} {t : Ω} {ν : ℝ}

theorem GlobalTheory.CompanionTheory.Ar.LieModel.isGrNorm_iff_formGramAt : M.IsGrNorm L V b₀ i z t ν ↔
    ∃ (h : genPt ξ ⤳ centre z) (b : Fin r → E) (Γ : Matrix (Fin r) (Fin r) ℂ),
      (∀ s, flagStep Ω b s = flagStep Ω b₀ s) ∧ V.IsFrameAt b ⟨centre z, h⟩ ∧ b i - t • b₀ i ∈ flagStep Ω b₀ i ∧
        M.FormGramAt L z b Γ ∧ Γ.PosDef ∧ ν = Real.sqrt (leadMinor Γ (i + 1) / leadMinor Γ i) := by sorry
