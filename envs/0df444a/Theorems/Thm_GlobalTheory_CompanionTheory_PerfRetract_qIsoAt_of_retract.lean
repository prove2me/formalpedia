-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PerfRetract_qIsoAt_of_retract
-- name    : GlobalTheory.CompanionTheory.PerfRetract.qIsoAt_of_retract
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:26:50.371097+00:00
-- url     : https://prove2.me/theorems/e1d9ab28-e754-475c-8c28-a8d3b6cd0a51
-- title:
--   Perf Retract: q Iso At of retract
-- statement:
--   The Perf Retract construction uses the q Iso At of retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HomotopyProjectorComplexBounded.lean#L15-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HomotopyProjectorComplexBounded.lean#L15-L63

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HomotopyProjectorComplexBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfRetract
variable {R : Type} [CommRing R] {K C E : ℕ → Type}
  [∀ p, AddCommGroup (K p)] [∀ p, AddCommGroup (C p)] [∀ p, AddCommGroup (E p)]
  [∀ p, Module R (K p)] [∀ p, Module R (C p)] [∀ p, Module R (E p)]

theorem GlobalTheory.CompanionTheory.PerfRetract.qIsoAt_of_retract
    (dK : ∀ p, K p →ₗ[R] K (p + 1)) (dC : ∀ p, C p →ₗ[R] C (p + 1))
    (dE : ∀ p, E p →ₗ[R] E (p + 1))
    (φ : ∀ p, K p →ₗ[R] C p) (inc : ∀ p, C p →ₗ[R] E p) (r : ∀ p, E p →ₗ[R] C p)
    (h : ∀ p, E (p + 1) →ₗ[R] E p)
    (hc : ConeExact (K := K) (C := C) (fun p => dK p) (fun p => dC p) (fun p => φ p))
    (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ dC p = dE p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ dE p = dC p ∘ₗ r p)
    (h0 : inc 0 ∘ₗ r 0 = LinearMap.id + h 0 ∘ₗ dE 0)
    (hs : ∀ p, inc (p + 1) ∘ₗ r (p + 1) =
      LinearMap.id + dE p ∘ₗ h p + h (p + 1) ∘ₗ dE (p + 1)) :
    QIsoAt (0 : R →ₗ[R] K 0) (dK 0) (0 : R →ₗ[R] E 0) (dE 0) (inc 0 ∘ₗ φ 0) ∧
    ∀ n, QIsoAt (dK n) (dK (n + 1)) (dE n) (dE (n + 1)) (inc (n + 1) ∘ₗ φ (n + 1)) := by sorry
