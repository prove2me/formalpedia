-- Prove2me | Theorems.Thm_FoundationsRL_OnlineLearning_eq_1_32
-- name    : FoundationsRL.OnlineLearning.eq_1_32
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:36.385119+00:00
-- url     : https://prove2.me/theorems/4f6189c7-ded5-44ef-a69d-e1bb785b1e6b
-- title:
--   (1.32) — the bounded-loss analysis summed over rounds
-- statement:
--   Let $\mathcal F$ be a finite nonempty class, let the losses $\ell(f(x),y)$ lie in $[0,1]$ for all $f\in\mathcal F$ and all $(x,y)$, and let $\eta>0$. Then
--   $$
--   \eta\sum_{t=1}^T\mathbb E_{\hat f^t\sim q^t}\big[\ell(\hat f^t(x^t),y^t)\big]\le\Phi^T_\eta-\Phi^0_\eta+\frac{T\eta^2}8.
--   $$
--
--   Summing the one-round inequality (1.31) turns the potential into a telescoping sum.
--
--   Differences from the source:
--   - encoding: expectation E_{f̂^t∼q^t} → the finite sum ∑ f ∈ F, q^t(f) ℓ(f(x^t), y^t); reason: q^t is a distribution on a finite class, so this is the same number
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (1.32), p. 17

import Mathlib
import Definitions.Def_FoundationsRL_OnlineLearning_ExponentialWeights

namespace FoundationsRL.OnlineLearning

/-- **(1.32) (the bounded-loss analysis summed over rounds).** Foster & Rakhlin, Foundations of
Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (1.32), p. 17.

For losses in `[0, 1]`,
`η ∑_{t=1}^T E_{f̂^t ∼ q^t}[ℓ(f̂^t(x^t), y^t)] ≤ Φ^T_η - Φ^0_η + Tη²/8`. -/
theorem eq_1_32 {X Y Y' : Type*} (F : Finset (X → Y')) (hF : F.Nonempty) (ℓ : Y' → Y → ℝ)
    (hℓ : ∀ f ∈ F, ∀ x y, ℓ (f x) y ∈ Set.Icc (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (x : ℕ → X) (y : ℕ → Y) (T : ℕ) :
    η * ∑ t ∈ Finset.range T, ∑ f ∈ F, ewDist ℓ F η x y t f * ℓ (f (x t)) (y t) ≤
      potential ℓ F η x y T - potential ℓ F η x y 0 + T * η ^ 2 / 8 := by sorry

end FoundationsRL.OnlineLearning
