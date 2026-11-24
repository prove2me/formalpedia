-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotLift_tsz_theta
-- name    : GlobalTheory.CompanionTheory.CotLift.tsz_theta
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:23:16.377801+00:00
-- url     : https://prove2.me/theorems/5a226bd6-996e-4a45-a55b-c77162c19754
-- title:
--   Cot Lift: tsz theta
-- statement:
--   The Cot Lift construction uses the tsz theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedImmersionUniversalSquareZero.lean#L114-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedImmersionUniversalSquareZero.lean#L114-L129

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
variable {R P B M : Type} [CommRing R] [CommRing P] [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] {α : R →+* P} {ε : P →+* R}

theorem GlobalTheory.CompanionTheory.CotLift.tsz_theta (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0)
    (φ : P →+* TrivSqZeroExt B M) (hα : φ.comp α = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B))
    (hf : ∀ a, (φ a).fst = algebraMap R B (ε a)) :
    (tsz (uOf φ hα hf)).comp (theta h hsq) = φ := by sorry
