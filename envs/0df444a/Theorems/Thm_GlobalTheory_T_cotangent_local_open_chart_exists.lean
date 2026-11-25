-- Prove2me | Theorems.Thm_GlobalTheory_T_cotangent_local_open_chart_exists
-- name    : GlobalTheory.T.cotangent_local_open_chart_exists
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:35:22.548512+00:00
-- url     : https://prove2.me/theorems/4287ca0d-d2c5-41b0-a135-9dbf0261c216
-- title:
--   T: cotangent local open chart exists
-- statement:
--   The T construction uses the cotangent local open chart exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExistsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExistsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExistsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cotangent_local_open_chart_exists : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X), e ≫ s = 𝟙 _ → ∀ (W : Type) [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W] (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ → ∀ (r : R) (A C : Type) [CommRing A] [CommRing C] [Algebra C A] [Algebra A (Localization.Away r)] (j : Sp A ⟶ X) (k : Sp C ⟶ Sp R) [IsOpenImmersion j] [Mono k], j ≫ s = spMap (algebraMap C A) ≫ k → spMap (algebraMap A (Localization.Away r)) ≫ j = spMap (algebraMap R (Localization.Away r)) ≫ e → Nonempty ((Localization.Away r ⊗[R] W) ≃ₗ[Localization.Away r] (Localization.Away r ⊗[A] KaehlerDifferential C A)) := by sorry
