-- Prove2me | Theorems.Thm_GlobalTheory_CompactAvgSchwartz_integral_tensor_matrix
-- name    : GlobalTheory.CompactAvgSchwartz.integral_tensor_matrix
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:04:35.65641+00:00
-- url     : https://prove2.me/theorems/df4b5290-17dc-5014-a335-0385b127df22
-- title:
--   Compact Avg Schwartz: integral tensor matrix
-- statement:
--   The Compact Avg Schwartz construction uses the integral tensor matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L258-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L258-L295

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchwartzIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.CompactAvgSchwartz

theorem GlobalTheory.CompactAvgSchwartz.integral_tensor_matrix {S R ι : Type} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
    [OpensMeasurableSpace S] [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [Fintype ι] {m n : ℕ} (ν : Measure S)
    [IsFiniteMeasure ν] (A Ai : S → ι → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ τ, Continuous fun s => A s τ)
    (hAi : ∀ τ, Continuous fun s => Ai s τ) (h : ∀ s τ, Ai s τ * A s τ = 1)
    (B Bi : S → Matrix (Fin m) (Fin m) R) (hB : Continuous B) (hBi : Continuous Bi) (h' : ∀ s, Bi s * B s = 1)
    (f : SchwartzMap (ι → Fin m → Fin n → ℂ) ℂ) {g : (Fin m → Fin n → R) → ℂ} (hg : g ∈ WeilM.SB (Fin m → Fin n → R)) :
    (∀ (x : ι → Fin m → Fin n → ℂ) (y : Fin m → Fin n → R),
      Integrable (fun s => f (fun τ i j => ∑ c, A s τ i c * x τ c j) * g (fun i j => ∑ c, B s i c * y c j)) ν) ∧
    ∃ (t : Finset ((Fin m → Fin n → R) → ℂ)) (F : ((Fin m → Fin n → R) → ℂ) → SchwartzMap (ι → Fin m → Fin n → ℂ) ℂ),
      (∀ g' ∈ t, g' ∈ WeilM.SB (Fin m → Fin n → R)) ∧
      ∀ (x : ι → Fin m → Fin n → ℂ) (y : Fin m → Fin n → R),
        ∫ s, f (fun τ i j => ∑ c, A s τ i c * x τ c j) * g (fun i j => ∑ c, B s i c * y c j) ∂ν =
          ∑ g' ∈ t, F g' x * g' y := by sorry
