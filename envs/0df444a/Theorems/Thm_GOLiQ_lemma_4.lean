-- Prove2me | Theorems.Thm_GOLiQ_lemma_4
-- name    : GOLiQ.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:08.834163+00:00
-- url     : https://prove2.me/theorems/abeeb9be-d316-47e7-8883-641f7170fc46
-- title:
--   Lemma 4 — smoothness of the steady-state waiting time in $(\mu,p)$
-- statement:
--   There is a constant $B>0$ such that for all $(\mu_1,p_1),(\mu_2,p_2)\in\mathcal B$ and all $1\le m\le4$, the steady-state waiting times coupled from the past on the same primitives satisfy
--   $$\mathbb E\big[|W_\infty(\mu_1,p_1)-W_\infty(\mu_2,p_2)|^m\big]\le B\big(|\mu_1-\mu_2|^m+|p_1-p_2|^m\big).$$
--
--   It bounds the change of the steady state between consecutive cycles, the second ingredient of the transient error.
--
--   Differences from the source:
--   - encoding: fee p > 0, service and arrival rates, the box [µ̲, µ̄] × [p̲, p̄] → 0 < µ̲ < µ̄, 0 < p̲ < p̄ and 0 < λ(p̄); reason: the fee is p > 0 (p.10) and rates are positive; λ′, c′ and ∇f on B are determined only when the intervals are nondegenerate
--   - encoding: λ and c continuously differentiable, with derivatives λ′ and c′ → C¹ on the closed intervals [p̲, p̄] and [µ̲, µ̄], λ′ and c′ the derivatives within them; reason: only values on the box enter the model
--   - encoding: U and V independent i.i.d. sequences with unit means; Z drawn in Algorithm 1 → nonnegative Uₙ, Vₙ and the draws Zₖ (uniform on {1, 2}) on one probability space, all mutually independent; reason: Uₙ/λ and Vₙ/µ are times; statements that do not mention Z do not depend on it
--   - generalization: the steady-state waiting times can be coupled such that the bound holds → the bound for the coupling by Loynes suprema on the same primitives; reason: it exhibits the coupling; the proof (p.58) uses this coupling from the past
--   - reading: 1 ≤ m ≤ 4 → real m with 1 ≤ m ≤ 4; reason: the proofs never use integrality of m; the real reading is the stronger one
--   - encoding: expectations of nonnegative quantities → lower Lebesgue integrals in [0, ∞]; reason: a finite bound then also asserts finiteness, and no junk value 0 arises for a non-integrable quantity
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Lemma 4, p.26; coupling, p.58

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_Assumption2
import Definitions.Def_GOLiQ_Model_objective

open MeasureTheory

namespace GOLiQ

/-- **Lemma 4 (smoothness in `µ` and `p`)** (Chen, Liu, Hong, arXiv:2009.02911v3, p.26): for
`(µᵢ, pᵢ) ∈ B`, `i = 1, 2`, the steady-state waiting times can be coupled so that, with a constant
`B > 0` independent of `(µᵢ, pᵢ)`, for all `1 ≤ m ≤ 4`,

`E[|W∞(µ₁, p₁) − W∞(µ₂, p₂)|^m] ≤ B (|µ₁ − µ₂|^m + |p₁ − p₂|^m)`.

**Formalization Note.** The coupling is the one of the proof (p.58): both stationary waiting times
are Loynes suprema over the same primitives `(U, V)` (`Model.stationaryWait`). `m` is real;
Assumptions 1–2 are standing. -/
theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω)
    (η θ a γ : ℝ) (h2 : Assumption2 M Pr η θ a γ) :
    ∃ B : ℝ, 0 < B ∧ ∀ mu₁ p₁ mu₂ p₂ : ℝ,
      mu₁ ∈ Set.Icc M.muLo M.muHi → p₁ ∈ Set.Icc M.pLo M.pHi →
      mu₂ ∈ Set.Icc M.muLo M.muHi → p₂ ∈ Set.Icc M.pLo M.pHi →
      ∀ m : ℝ, 1 ≤ m → m ≤ 4 →
        ∫⁻ ω, ENNReal.ofReal
            (|M.stationaryWait Pr mu₁ p₁ ω - M.stationaryWait Pr mu₂ p₂ ω| ^ m) ∂Pr.P ≤
          ENNReal.ofReal (B * (|mu₁ - mu₂| ^ m + |p₁ - p₂| ^ m)) := by sorry

end GOLiQ
