-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_lemma_B_4
-- name    : OrderSelProphet.Kernel.lemma_B_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:57:08.554954+00:00
-- url     : https://prove2.me/theorems/7e87372d-1a97-46cb-b4b0-11ce0c0f3e8a
-- title:
--   Lemma B.4 — realizability: every finite family of profiles summing to one a.e. is the profile family of an atomless input
-- statement:
--   Let $\lambda_1,\dots,\lambda_n:[0,1]\to[0,1]$ be measurable with $\sum_i\lambda_i=1$ almost everywhere. Then there are independent, atomless, nonnegative random values $V_1,\dots,V_n$ whose profiles are $\lambda_1,\dots,\lambda_n$, up to null sets. In particular, every profile $\lambda\in\Lambda$ is realized in a two-item input with profiles $(\lambda,1-\lambda)$.
--
--   Differences from the source:
--   - encoding: Λ: measurable λ : [0,1] → [0,1], identified when equal a.e. → Profile: measurable functions ℝ → ℝ with values in [0,1] on [0,1]; quantifying over representatives; reason: every quantity depends only on the a.e. class on [0,1]; a measurable function on [0,1] extends measurably to ℝ
--   - encoding: independent atomless nonnegative V_1, …, V_n whose profiles are λ_i up to null sets → laws F_i (probability measures) forming an atomless input with IsProfileOf F i λ_i for every i; reason: independence is built into the product law used by IsProfileOf; (10) determines a profile only up to null sets
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Lemma B.4, p. 41

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Profiles

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Lemma B.4 (Realizability), p. 41: every finite family of measurable `[0,1]`-valued profiles
summing to one almost everywhere is the profile family of an atomless input; in particular every
profile `λ` is realized in a two-item input with profiles `(λ, 1 - λ)`. -/
theorem lemma_B_4 {n : ℕ} (lams : Fin n → ℝ → ℝ) (hmeas : ∀ i, Measurable (lams i))
    (hval : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, lams i u ∈ Icc (0 : ℝ) 1)
    (hsum : ∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) 1)), ∑ i, lams i u = 1) :
    (∃ (F : Fin n → Measure ℝ) (_ : ∀ i, IsProbabilityMeasure (F i)),
        IsAtomlessInput F ∧ ∀ i, IsProfileOf F i (lams i)) ∧
      ∀ lam : Profile, ∃ (F : Fin 2 → Measure ℝ) (_ : ∀ i, IsProbabilityMeasure (F i)),
        IsAtomlessInput F ∧ IsProfileOf F 0 lam.1 ∧ IsProfileOf F 1 (fun u => 1 - lam.1 u) := by sorry

end OrderSelProphet.Kernel
