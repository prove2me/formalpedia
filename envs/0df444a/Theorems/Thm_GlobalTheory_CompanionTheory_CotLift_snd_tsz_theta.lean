-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotLift_snd_tsz_theta
-- name    : GlobalTheory.CompanionTheory.CotLift.snd_tsz_theta
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:22:41.974418+00:00
-- url     : https://prove2.me/theorems/7daae660-13a7-4d94-b6f5-e35f14a8a7b5
-- title:
--   Cot Lift: snd tsz theta
-- statement:
--   The Cot Lift construction uses the snd tsz theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedImmersionUniversalSquareZero.lean#L131-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedImmersionUniversalSquareZero.lean#L131-L135

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

theorem GlobalTheory.CompanionTheory.CotLift.snd_tsz_theta (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0)
    (u : KerW α ε →ₗ[R] M) (w : KerW α ε) : ((tsz (B := B) u).comp (theta h hsq) w.val).snd = u w := by sorry
