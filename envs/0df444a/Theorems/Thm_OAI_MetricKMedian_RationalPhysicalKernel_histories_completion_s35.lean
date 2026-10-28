-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_completion_s35
-- name    : OAI.MetricKMedian.RationalPhysicalKernel.histories_completion_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:46:19.256795+00:00
-- url     : https://prove2.me/theorems/56e7485f-76c7-4d02-91a6-a8b97ce1ca6f
-- title:
--   OAI.MetricKMedian.RationalPhysicalKernel.histories_completion_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalPhysicalKernel`, with `open Finset PhysicalPotential CopyState Completion.Rational`):
--
--   ```lean
--   theorem histories_completion_s35 (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
--       (location : F → X) (client : Fin j → X)
--       (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
--       (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
--       (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
--       (A : Finset (Copy (F := F) Δ)) (B : Fin j → Finset (Copy (F := F) Δ))
--       (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty) (T : ℕ) (x : ℕ → ℝ)
--       (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
--       (hA : 1 ≤ mass (g:ℝ) A) (hBA : ∀ c, B c⊆A)
--       (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (g:ℝ) (B c)=1)
--       (hdR : ∀ c i, i∈B c → d c i.1≤R c)
--       (a : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) :
--       let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val];
--       let O := completed d R B hB g β z;
--       ((O.card:ℝ)≤ mass (g:ℝ) z.1.1) ∧
--       (0<j → O.Nonempty) ∧
--       (score d O:ℝ) ≤ ∑ c, (
--         potential (x T) (g:ℝ) (fun i : Copy (F := F) Δ => dist (client c) (location i.1))
--           (replay g β x (fun (_ : Unit) f => dist (client c) (location f)) (fun _ => B c) z ())
--           (GroupCap.cap (R c:ℝ) (fun f => dist (client c) (location f)) (integral Δ z.1.1))+
--         5*(R c:ℝ)*mass (g:ℝ)
--           (replay g β x (fun (_ : Unit) f => dist (client c) (location f)) (fun _ => B c) z ()))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Completion.Rational.score` (definitions bundle `OAIQ035K002` of this split); `OAI.MetricKMedian.CopyState.Copy`, `OAI.MetricKMedian.CopyState.integral` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.SparseHistories.History` (definitions bundle `OAIQ035K005` of this split); `OAI.MetricKMedian.GroupCap.cap` (definitions bundle `OAIQ035K008` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.Payload`, `OAI.MetricKMedian.RationalPhysicalKernel.State` and `OAI.MetricKMedian.SparseIntegerLaw` (definitions bundle `OAIQ035K017` of this split); `OAI.MetricKMedian.PhysicalPotential.potential` (definitions bundle `OAIQ035K021` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.completed` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.replay` (definitions bundle `OAIQ035K044` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.histories` (definitions bundle `OAIQ035K047` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_s35` and `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_s35` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K047

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential CopyState Completion.Rational
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j Δ : ℕ}

theorem histories_completion_s35 (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (Copy (F := F) Δ)) (B : Fin j → Finset (Copy (F := F) Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty) (T : ℕ) (x : ℕ → ℝ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hBA : ∀ c, B c⊆A)
    (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1≤R c)
    (a : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) :
    let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val];
    let O := completed d R B hB g β z;
    ((O.card:ℝ)≤ mass (g:ℝ) z.1.1) ∧
    (0<j → O.Nonempty) ∧
    (score d O:ℝ) ≤ ∑ c, (
      potential (x T) (g:ℝ) (fun i : Copy (F := F) Δ => dist (client c) (location i.1))
        (replay g β x (fun (_ : Unit) f => dist (client c) (location f)) (fun _ => B c) z ())
        (GroupCap.cap (R c:ℝ) (fun f => dist (client c) (location f)) (integral Δ z.1.1))+
      5*(R c:ℝ)*mass (g:ℝ)
        (replay g β x (fun (_ : Unit) f => dist (client c) (location f)) (fun _ => B c) z ())) := by
  sorry

end MetricKMedian.RationalPhysicalKernel
end

end OAI
end
