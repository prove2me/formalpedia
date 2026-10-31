-- Prove2me | Theorems.Thm_FoundationsRL_OnlineLearning_proposition_3
-- name    : FoundationsRL.OnlineLearning.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:41.504879+00:00
-- url     : https://prove2.me/theorems/39817788-8d90-48c4-88ac-9135301e6f6e
-- title:
--   Proposition 3 — Exponential Weights regret $\lesssim\sqrt{T\log|\mathcal F|}$ (bounded), $\lesssim\log|\mathcal F|$ (square, log) (corrected: square loss on $[0,1]$)
-- statement:
--   Let $\mathcal F$ be a finite nonempty class, and let $(x^t,y^t)_{t\ge1}$ be any data sequence. The Exponential Weights algorithm with a suitable learning rate satisfies the following.
--
--   1. **Bounded losses, randomized variant.** If $\ell(f(x),y)\in[a,b]$ for all $f\in\mathcal F$ and all $(x,y)$, then with $\eta=\sqrt{8\log|\mathcal F|/T}/(b-a)$,
--   $$
--   \sum_{t=1}^T\mathbb E_{\hat f^t\sim q^t}\big[\ell(\hat f^t(x^t),y^t)\big]-\min_{f\in\mathcal F}\sum_{t=1}^T\ell(f(x^t),y^t)\le(b-a)\sqrt{\frac{T\log|\mathcal F|}2}.
--   $$
--   2. **Square loss, averaged variant.** If $f(x)\in[0,1]$ for all $f\in\mathcal F$ and all $x$, and $y^t\in[0,1]$ for all $t$, then with $\eta=\tfrac12$,
--   $$
--   \sum_{t=1}^T(\hat f^t(x^t)-y^t)^2-\min_{f\in\mathcal F}\sum_{t=1}^T(f(x^t)-y^t)^2\le2\log|\mathcal F|.
--   $$
--   3. **Log loss, averaged variant.** If $\mathcal F$ consists of conditional densities, then with $\eta=1$,
--   $$
--   \sum_{t=1}^T\ell_{\log}(\hat f^t(x^t),y^t)\le\min_{f\in\mathcal F}\sum_{t=1}^T\ell_{\log}(f(x^t),y^t)+\log|\mathcal F|.
--   $$
--
--   Dividing by $T$ gives $\frac1T\mathbf{Reg}\lesssim\mathrm{comp}(\mathcal F,T)$ with $\mathrm{comp}(\mathcal F,T)=\sqrt{\log|\mathcal F|/T}$ in the first case and $\log|\mathcal F|/T$ in the other two. These rates parallel those of empirical risk minimization, with no assumption on the data sequence.
--
--   **Formalization Note** Every bound holds for every sequence, so an adaptive adversary is covered: the algorithm is a deterministic function of the past, and for the randomized variant the regret is the one with the expectation over $q^t$. Log losses lie in $(-\infty,+\infty]$; the third bound is stated additively because a difference of two infinite losses is undefined. Degenerate learning rates ($|\mathcal F|=1$, $T=0$, $a=b$) are $0$ in Lean, $q^t$ is then uniform, and the bounds still hold.
--
--   Differences from the source:
--   - correction: square loss regression with any Y, comp(F, T) = log|F|/T → f(x), y ∈ [0, 1], the range of Remark 6; reason: false on Y = ℝ with an absolute constant: X a point, F = {0, c}, T = 1; an adversary playing y = c or 0, whichever is farther from the prediction, gives Reg ≥ c²/4, which exceeds C log 2 for large c
--   - generalization: (1/T) Reg ≲ comp(F, T) with unspecified η → explicit η and constants: Reg ≤ (b − a)√(T log|F|/2), Reg ≤ 2 log|F|, and Reg ≤ log|F|; reason: explicit bounds imply the printed rates, with absolute constants for fixed loss range, on dividing by T ≥ 1
--   - generalization: f(·|x) a density on Y → f : X → Y → ℝ any nonnegative function; reason: the argument uses only nonnegativity, and densities are nonnegative functions
--   - encoding: ℓ_log = −log f(y|x), exp{−∑ℓ_log} → values in EReal with −log 0 = +∞, and weights written as the likelihood product; reason: a zero density has infinite loss, and exp(−∞) = 0 makes the two weight formulas agree
--   - encoding: Reg ≲ for the log loss → Σ alg ≤ min Σ f + log|F| in EReal, not a difference; reason: ⊤ − ⊤ = ⊥ in EReal, and the notes’ difference is undefined when every expert has infinite loss; the two forms agree when the minimum is finite
--   - encoding: expectation E_{f̂^t∼q^t} → the finite sum ∑ f ∈ F, q^t(f) ℓ(f(x^t), y^t); reason: q^t is a distribution on a finite class, so this is the same number
--   - encoding: rounds t = 1, …, T → 0-based rounds in Finset.range T; reason: Lean convention; same instances
--   - encoding: η > 0 → η = 0 in Lean when |F| = 1, T = 0 or a = b; reason: degenerate cases in which the notes’ formula is undefined or trivial; q^t is uniform and the bound still holds
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 3, p. 16; proof pp. 16–18; Remark 6, pp. 18–19

import Mathlib
import Definitions.Def_FoundationsRL_OnlineLearning_Protocol
import Definitions.Def_FoundationsRL_OnlineLearning_Losses
import Definitions.Def_FoundationsRL_OnlineLearning_ExponentialWeights
import Definitions.Def_FoundationsRL_OnlineLearning_LogLossWeights

namespace FoundationsRL.OnlineLearning

/-- **Proposition 3 (regret of Exponential Weights), square-loss range corrected.** Foster & Rakhlin,
Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 3,
p. 16, with the proof on pp. 16–18 and Remark 6, pp. 18–19.

For any finite nonempty class `F` and every data sequence:
1. for any loss with values in `[a, b]` on `F`, the randomized variant with
   `η = √(8 log|F| / T) / (b - a)` has `Reg ≤ (b - a) √(T log|F| / 2)`;
2. for the square loss with `f(x), y ∈ [0, 1]`, the averaged variant with `η = 1/2` has
   `Reg ≤ 2 log|F|`;
3. for the log loss, the averaged variant with `η = 1` has `Reg ≤ log|F|`.

**Formalization Note.** The notes' `(1/T) Reg ≲ comp(F, T)` is stated with explicit constants, in the
form `Reg ≤ T · C · comp(F, T)`, which also covers `T = 0`. Clause 2 carries the range `[0, 1]` that
the notes' Remark 6 uses, since the printed statement is false on `Y = ℝ`. In clause 3 densities may
vanish, so log losses are in `EReal`. There `Reg` is stated additively: `⊤ - ⊤ = ⊥` in `EReal`, and when
every expert has infinite loss the notes' difference is undefined. The degenerate `η` values (`|F| = 1`,
`T = 0`, `a = b`) are `0` in Lean, `q^t` is then uniform, and the bound still holds. -/
theorem proposition_3 {X Y Y' : Type*} :
    (∀ (F : Finset (X → Y')) (_ : F.Nonempty) (ℓ : Y' → Y → ℝ) (a b : ℝ) (_ : a ≤ b)
        (_ : ∀ f ∈ F, ∀ x y, ℓ (f x) y ∈ Set.Icc a b) (T : ℕ) (x : ℕ → X) (y : ℕ → Y),
      regretRandomized ℓ F (ewDist ℓ F (Real.sqrt (8 * Real.log F.card / T) / (b - a)) x y) x y T ≤
        (b - a) * Real.sqrt (T * Real.log F.card / 2)) ∧
    (∀ (F : Finset (X → ℝ)) (_ : F.Nonempty) (_ : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
        (T : ℕ) (x : ℕ → X) (y : ℕ → ℝ) (_ : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1),
      regret squareLoss (F : Set (X → ℝ))
          (fun t => ewAveraged F (ewDist squareLoss F (1 / 2) x y t)) x y T ≤
        2 * Real.log F.card) ∧
    (∀ (F : Finset (X → Y → ℝ)) (_ : F.Nonempty) (_ : ∀ f ∈ F, ∀ x y, 0 ≤ f x y)
        (T : ℕ) (x : ℕ → X) (y : ℕ → Y),
      cumLoss logLoss (fun t => ewAveraged F (logDist F x y t)) x y T ≤
        bestCumLoss logLoss (F : Set (X → Y → ℝ)) x y T + ((Real.log F.card : ℝ) : EReal)) := by sorry

end FoundationsRL.OnlineLearning
