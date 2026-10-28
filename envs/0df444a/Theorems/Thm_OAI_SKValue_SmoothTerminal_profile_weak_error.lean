-- Prove2me | Theorems.Thm_OAI_SKValue_SmoothTerminal_profile_weak_error
-- name    : OAI.SKValue.SmoothTerminal.profile_weak_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:49:42.900777+00:00
-- url     : https://prove2.me/theorems/c5e66fc3-3624-4487-93f5-7929d8235634
-- title:
--   OAI.SKValue.SmoothTerminal.profile_weak_error: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.SmoothTerminal.profile_weak_error` of [lean/OAI/Probability/SKValue/SKValue/Gaussian/ProfileLawStability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Gaussian/ProfileLawStability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology NNReal`):
--
--   ```lean
--   lemma SmoothTerminal.profile_weak_error {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
--       [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hBrown:IsPreBrownianReal B μ)
--       {X:ℝ → Ω → ℝ} {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
--       {l:HeatProfile} (hl:l.Pairwise (fun p q ↦ p.2≤q.2)) {T K L Lu a b H:ℝ}
--       (hTl:profileTime l=T) (hT:0<T) (hT1:T≤1) {γ:ℝ → ℝ} {u:ℝ → ℝ → ℝ}
--       (hu:GradientStrip T γ u K L) (hLu:0≤Lu)
--       (hLip:∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x y,|u s x-u t y|≤Lu*(|s-t|+|x-y|))
--       (ha:0≤a) (hb:0≤b) (hH:0≤H)
--       (hc:∀ t∈Icc (0:ℝ) T,profileCoeff l t≤γ t+a)
--       (hs:∀ t∈Icc (0:ℝ) T,∀ x,|deriv (profileValue ψ l t) x-u t x|≤b)
--       (hfl:∀ x y,|f x-f y|≤H*|x-y|)
--       (hXM:∀ t∈Icc (0:ℝ) T,MemLp (X t) 2 μ)
--       (hpaths:∀ᵐ ω ∂μ,ContinuousOn (fun t ↦ X t ω) (Icc (0:ℝ) T) ∧
--         IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
--         (∀ t∈Icc (0:ℝ) T,X t ω=B t.toNNReal ω+∫ s in (0:ℝ)..t,γ s*u s (X s ω)) ∧ X 0 ω=0) :
--       |(∫ ω,f (X T ω) ∂μ)-profileResponse ψ f l 0 0|≤
--         H*((∫ t in (0:ℝ)..T,γ t)-(∫ t in (0:ℝ)..T,profileCoeff l t)+T*(2*a+γ T*b))*Real.exp (T*γ T*Lu)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.BoundedSmooth`, `OAI.SKValue.GradientStrip`, `OAI.SKValue.HeatProfile`, `OAI.SKValue.SmoothTerminal`, `OAI.SKValue.profileCoeff`, `OAI.SKValue.profileResponse`, `OAI.SKValue.profileTime` and `OAI.SKValue.profileValue` (definitions bundle `OAIQ4Sk000` of this split).
--
--   **Used by.** The proof of `OAI.SKValue.IsDiffusion.splitResponse_tendsto` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Gaussian/ProfileLawStability.lean (declaration OAI.SKValue.SmoothTerminal.profile_weak_error)

import Mathlib
import Definitions.Def_OAIQ4Sk000

section

attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma SmoothTerminal.profile_weak_error {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hBrown:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {l:HeatProfile} (hl:l.Pairwise (fun p q ↦ p.2≤q.2)) {T K L Lu a b H:ℝ}
    (hTl:profileTime l=T) (hT:0<T) (hT1:T≤1) {γ:ℝ → ℝ} {u:ℝ → ℝ → ℝ}
    (hu:GradientStrip T γ u K L) (hLu:0≤Lu)
    (hLip:∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x y,|u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (ha:0≤a) (hb:0≤b) (hH:0≤H)
    (hc:∀ t∈Icc (0:ℝ) T,profileCoeff l t≤γ t+a)
    (hs:∀ t∈Icc (0:ℝ) T,∀ x,|deriv (profileValue ψ l t) x-u t x|≤b)
    (hfl:∀ x y,|f x-f y|≤H*|x-y|)
    (hXM:∀ t∈Icc (0:ℝ) T,MemLp (X t) 2 μ)
    (hpaths:∀ᵐ ω ∂μ,ContinuousOn (fun t ↦ X t ω) (Icc (0:ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0:ℝ) T,X t ω=B t.toNNReal ω+∫ s in (0:ℝ)..t,γ s*u s (X s ω)) ∧ X 0 ω=0) :
    |(∫ ω,f (X T ω) ∂μ)-profileResponse ψ f l 0 0|≤
      H*((∫ t in (0:ℝ)..T,γ t)-(∫ t in (0:ℝ)..T,profileCoeff l t)+T*(2*a+γ T*b))*Real.exp (T*γ T*Lu) := by
  sorry
end SKValue

end

end OAI
end
