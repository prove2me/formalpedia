-- Prove2me | Theorems.Thm_FoundationsRL_OnlineLearning_lemma_6
-- name    : FoundationsRL.OnlineLearning.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:45.53786+00:00
-- url     : https://prove2.me/theorems/0df4516c-b91c-4f6e-af59-43f6052172fe
-- title:
--   Lemma 6 — for well-specified square loss, $\mathbb E[\mathbf{Reg}]\ge\mathbb E[\sum_t(\hat f^t(x^t)-f^\star(x^t))^2]$
-- statement:
--   Let the features $x^1,\dots,x^T$ be generated in an arbitrary fashion, and let $f^\star\in\mathcal F$ be a fixed function such that, given everything available when the prediction at round $t$ is made, $y^t$ has mean $f^\star(x^t)$:
--   $$
--   \mathbb E[y^t\mid\mathcal G_t]=f^\star(x^t).
--   $$
--   Then for prediction with square loss,
--   $$
--   \mathbb E[\mathbf{Reg}]\ge\mathbb E\Big[\sum_{t=1}^T\big(\hat f^t(x^t)-f^\star(x^t)\big)^2\Big].
--   $$
--
--   So a regret bound for square loss is an estimation guarantee, even when the features are chosen adversarially.
--
--   **Formalization Note** $(\mathcal G_t)$ is a filtration in which each prediction $\hat f^t(x^t)$ is $\mathcal G_t$-measurable. Outcomes and predictions are square-integrable, which keeps both sides finite.
--
--   Differences from the source:
--   - reading: E[y^t | x^t = x] = f⋆(x) → E[y^t | 𝓖 t] = f⋆(x^t) for a filtration 𝓖 with f̂^t(x^t) 𝓖 t-measurable; reason: conditioning on x^t alone makes the lemma false: x constant, F = {0}, T = 2, y^1 = ±1 fair, y^2 = y^1, f̂^1 = 0, f̂^2 = y^1 gives E[Reg] = −1 and right side 1; the notes’ remark about adversarial features needs the history in the conditioning
--   - encoding: outcomes random, expectations → y^t and f̂^t(x^t) in L², and Reg integrable; reason: the notes assume the expectations exist; a Bochner integral of a non-integrable function would be 0
--   - encoding: rounds t = 1, …, T → 0-based rounds in Finset.range T; reason: Lean convention; same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 6, p. 15

import Mathlib
import Definitions.Def_FoundationsRL_OnlineLearning_Protocol
import Definitions.Def_FoundationsRL_OnlineLearning_Losses

open MeasureTheory

namespace FoundationsRL.OnlineLearning

/-- **Lemma 6 (regret dominates estimation error for well-specified square loss).** Foster & Rakhlin,
Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 6,
p. 15.

If the features are generated in an arbitrary fashion and `y^t` has mean `f⋆(x^t)` for a fixed
`f⋆ ∈ F`, then for prediction with square loss
`E[Reg] ≥ E[∑_{t=1}^T (f̂^t(x^t) - f⋆(x^t))²]`.

**Formalization Note.** `𝓖 t` is the information available when `f̂^t` is formed and `x^t` is revealed,
so the prediction `f̂^t(x^t)` is `𝓖 t`-measurable, and the mean condition is conditional on all of it:
`E[y^t | 𝓖 t] = f⋆(x^t)`. Conditioning on `x^t` alone would not suffice (see the differences list).
`X` carries no σ-algebra: the features may be arbitrary. Square-integrability keeps both sides finite,
and `hReg` makes `E[Reg]` genuine over an infinite class. The infimum in `Reg` is over nonnegative
sums, so it is bounded below, and `F` is nonempty since it holds `f⋆`. -/
theorem lemma_6 {X Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓖 : Filtration ℕ mΩ) (F : Set (X → ℝ)) (fstar : X → ℝ) (hfstar : fstar ∈ F) (T : ℕ)
    (x : ℕ → Ω → X) (y : ℕ → Ω → ℝ) (fhat : ℕ → Ω → X → ℝ)
    (hy : ∀ t, MemLp (y t) 2 P)
    (hfhatm : ∀ t, StronglyMeasurable[𝓖 t] fun ω => fhat t ω (x t ω))
    (hfhat : ∀ t, MemLp (fun ω => fhat t ω (x t ω)) 2 P)
    (hmean : ∀ t, P[y t | 𝓖 t] =ᵐ[P] fun ω => fstar (x t ω))
    (hReg : Integrable (fun ω =>
      regret squareLoss F (fun t => fhat t ω) (fun t => x t ω) (fun t => y t ω) T) P) :
    ∫ ω, ∑ t ∈ Finset.range T, (fhat t ω (x t ω) - fstar (x t ω)) ^ 2 ∂P ≤
      ∫ ω, regret squareLoss F (fun t => fhat t ω) (fun t => x t ω) (fun t => y t ω) T ∂P := by sorry

end FoundationsRL.OnlineLearning
