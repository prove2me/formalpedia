-- Prove2me | Theorems.Thm_FoundationsRL_OnlineLearning_eq_1_33
-- name    : FoundationsRL.OnlineLearning.eq_1_33
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:43.167518+00:00
-- url     : https://prove2.me/theorems/536cf670-b2a9-407f-a4a4-5b19c6b94624
-- title:
--   (1.33) — tuned bounded-loss regret $\le\sqrt{T\log|\mathcal F|/2}$
-- statement:
--   Let $\mathcal F$ be a finite nonempty class and let the losses $\ell(f(x),y)$ lie in $[0,1]$ for all $f\in\mathcal F$ and all $(x,y)$. With $\eta=\sqrt{8\log|\mathcal F|/T}$, for any $f^\star\in\mathcal F$,
--   $$
--   \sum_{t=1}^T\Big(\mathbb E_{\hat f^t\sim q^t}\big[\ell(\hat f^t(x^t),y^t)\big]-\ell(f^\star(x^t),y^t)\Big)\le\sqrt{\frac{T\log|\mathcal F|}2}.
--   $$
--
--   This is the explicit form of the slow rate in Proposition 3.
--
--   **Formalization Note** For $|\mathcal F|=1$ or $T=0$ this $\eta$ is $0$ in Lean, $q^t$ is uniform, and both sides vanish.
--
--   Differences from the source:
--   - encoding: expectation E_{f̂^t∼q^t} → the finite sum ∑ f ∈ F, q^t(f) ℓ(f(x^t), y^t); reason: q^t is a distribution on a finite class, so this is the same number
--   - encoding: η > 0 → η = √(8 log|F|/T), which is 0 when |F| = 1 or T = 0; reason: those cases are undefined or degenerate in the notes, and the definition of q^t still makes sense there
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (1.33), p. 18

import Mathlib
import Definitions.Def_FoundationsRL_OnlineLearning_ExponentialWeights

namespace FoundationsRL.OnlineLearning

/-- **(1.33) (explicit bounded-loss regret).** Foster & Rakhlin, Foundations of Reinforcement Learning
and Interactive Decision Making, arXiv:2312.16730v1, (1.33), p. 18.

For losses in `[0, 1]`, with `η = √(8 log|F| / T)`, and for any `f⋆ ∈ F`,
`∑_{t=1}^T (E_{f̂^t ∼ q^t}[ℓ(f̂^t(x^t), y^t)] - ℓ(f⋆(x^t), y^t)) ≤ √(T log|F| / 2)`.

**Formalization Note.** For `|F| = 1` or `T = 0` this `η` is `0` in Lean (`x / 0 = 0`), `q^t` is
uniform, and both sides are `0`, so the degenerate cases are included. -/
theorem eq_1_33 {X Y Y' : Type*} (F : Finset (X → Y')) (hF : F.Nonempty) (ℓ : Y' → Y → ℝ)
    (hℓ : ∀ f ∈ F, ∀ x y, ℓ (f x) y ∈ Set.Icc (0 : ℝ) 1)
    (x : ℕ → X) (y : ℕ → Y) (T : ℕ) (fstar : X → Y') (hfstar : fstar ∈ F) :
    ∑ t ∈ Finset.range T,
        (∑ f ∈ F, ewDist ℓ F (Real.sqrt (8 * Real.log F.card / T)) x y t f * ℓ (f (x t)) (y t) -
          ℓ (fstar (x t)) (y t)) ≤
      Real.sqrt (T * Real.log F.card / 2) := by sorry

end FoundationsRL.OnlineLearning
