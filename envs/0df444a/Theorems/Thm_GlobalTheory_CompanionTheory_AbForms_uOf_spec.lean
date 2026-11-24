-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_uOf_spec
-- name    : GlobalTheory.CompanionTheory.AbForms.uOf_spec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:22:05.649183+00:00
-- url     : https://prove2.me/theorems/449d89aa-62db-45a8-9f2e-7efe0b962bf7
-- title:
--   Ab Forms: u Of spec
-- statement:
--   The Ab Forms construction uses the u Of spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UOfIsBaseChange.lean#L218-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UOfIsBaseChange.lean#L218-L219

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]
variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
  [IsCentralScalar R W] {y₀ : Sp (TrivSqZeroExt R W) ⟶ A.left} (hy : IsCot A.hom η[A].left W y₀)
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M']
variable (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B))

theorem GlobalTheory.CompanionTheory.AbForms.uOf_spec : Zp x hx (diagSec R B : B →+* _) diag_w = tzo (B := B) (M := Ω[B⁄R]) hy (uOf hy x hx) := by sorry
