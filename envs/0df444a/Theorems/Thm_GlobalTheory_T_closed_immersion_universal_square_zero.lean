-- Prove2me | Theorems.Thm_GlobalTheory_T_closed_immersion_universal_square_zero
-- name    : GlobalTheory.T.closed_immersion_universal_square_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:03.340196+00:00
-- url     : https://prove2.me/theorems/92657ee1-3d84-41e9-ac98-33cb1c2bb3a4
-- title:
--   T: closed immersion universal square zero
-- statement:
--   The T construction uses the closed immersion universal square zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedImmersionUniversalSquareZeroStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedImmersionUniversalSquareZeroStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZero
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZeroStatement
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

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

theorem GlobalTheory.T.closed_immersion_universal_square_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (P : Type) [CommRing P] (α : R →+* P) (ε : P →+* R) (j : Sp P ⟶ X), ε.comp α = RingHom.id R → (∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) → j ≫ s = spMap α → spMap ε ≫ j = e → Mono j → (∀ (Q B : Type) [CommRing Q] [CommRing B] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ X), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → ∃ φ : P →+* Q, spMap φ ≫ j = y) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W) (_ : Module Rᵐᵒᵖ W) (_ : IsCentralScalar R W) (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ := by sorry
