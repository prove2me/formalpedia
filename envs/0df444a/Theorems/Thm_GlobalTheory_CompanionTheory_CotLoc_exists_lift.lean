-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_exists_lift
-- name    : GlobalTheory.CompanionTheory.CotLoc.exists_lift
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:58:12.833542+00:00
-- url     : https://prove2.me/theorems/c571149d-d458-47c0-bb2c-96cda072f215
-- title:
--   Cot Loc: exists lift
-- statement:
--   The Cot Loc construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L181-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L181-L203

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {e : Sp R ⟶ X}
  {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W]
  {y₀ : Sp (TrivSqZeroExt R W) ⟶ X}
  {R' : Type} [CommRing R'] [Algebra R R'] {A C : Type} [CommRing A] [CommRing C] [Algebra C A]
  [Algebra A R'] {j : Sp A ⟶ X} {k : Sp C ⟶ Sp R}
variable {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
  [Module R M] [IsScalarTower R R' M]
variable {N : Type} [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [Module R N] [IsScalarTower R R' N]

theorem GlobalTheory.CompanionTheory.CotLoc.exists_lift (ψ : A →+* TrivSqZeroExt R' M) (hψ : Good (C := C) ψ) :
    ∃ v : (R' ⊗[A] KaehlerDifferential C A) →ₗ[R'] M,
      ∀ a, v (1 ⊗ₜ KaehlerDifferential.D C A a) = (ψ a).snd := by sorry
