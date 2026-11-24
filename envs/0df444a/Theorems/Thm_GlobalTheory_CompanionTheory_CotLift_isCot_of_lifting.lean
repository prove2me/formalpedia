-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotLift_isCot_of_lifting
-- name    : GlobalTheory.CompanionTheory.CotLift.isCot_of_lifting
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:22:28.337706+00:00
-- url     : https://prove2.me/theorems/dda61ec3-1506-4f70-8e9a-81d28f006ef1
-- title:
--   Cot Lift: is Cot of lifting
-- statement:
--   The Cot Lift construction uses the is Cot of lifting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedImmersionUniversalSquareZero.lean#L139-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedImmersionUniversalSquareZero.lean#L139-L175

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLift

theorem GlobalTheory.CompanionTheory.CotLift.isCot_of_lifting : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (P : Type) [CommRing P] (α : R →+* P) (ε : P →+* R) (j : Sp P ⟶ X), ε.comp α = RingHom.id R → (∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) → j ≫ s = spMap α → spMap ε ≫ j = e → Mono j → (∀ (Q B : Type) [CommRing Q] [CommRing B] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ X), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → ∃ φ : P →+* Q, spMap φ ≫ j = y) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W) (_ : Module Rᵐᵒᵖ W) (_ : IsCentralScalar R W) (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ := by sorry
