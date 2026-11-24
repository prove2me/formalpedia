-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_tw_nat
-- name    : GlobalTheory.CompanionTheory.PerfExt.tw_nat
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:35.735675+00:00
-- url     : https://prove2.me/theorems/ed324cc9-eeeb-4a19-8c93-77bece46f0f7
-- title:
--   Perf Ext: tw nat
-- statement:
--   The Perf Ext construction uses the tw nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/D2Apply.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/D2Apply.lean#L43-L49

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfExt
variable (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
variable {R R'}
variable {N N₂ Q Q₂ M : Type} [AddCommGroup N] [Module R N] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup Q] [Module R' Q] [AddCommGroup Q₂] [Module R' Q₂]
  [AddCommGroup M] [Module R' M] [Module R M] [IsScalarTower R R' M]

theorem GlobalTheory.CompanionTheory.PerfExt.tw_nat (E : R' ⊗[R] N ≃ₗ[R'] Q) (E₂ : R' ⊗[R] N₂ ≃ₗ[R'] Q₂) (g : N →ₗ[R] N₂) (h : Q →ₗ[R'] Q₂)
    (H : ∀ n, h (E (1 ⊗ₜ n)) = E₂ (1 ⊗ₜ g n)) (t : M ⊗[R] N) :
    tw M E₂ (g.lTensor M t) = h.lTensor M (tw M E t) := by sorry
