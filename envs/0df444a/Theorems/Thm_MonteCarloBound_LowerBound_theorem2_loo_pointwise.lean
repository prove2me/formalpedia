-- Prove2me | Theorems.Thm_MonteCarloBound_LowerBound_theorem2_loo_pointwise
-- name    : MonteCarloBound.LowerBound.theorem2_loo_pointwise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:18.407142+00:00
-- url     : https://prove2.me/theorems/ec68745b-c080-4e77-ab52-d7a6bdb08980
-- title:
--   Proof of Theorem 2, p. 50 — min of the average ≥ average of the leave-one-out minima
-- statement:
--   Let $X\subseteq\mathbb R^d$ be nonempty, $f$ real valued, $n\ge1$, and let $\tilde\xi^1,\dots,\tilde\xi^{n+1}$ be fixed realizations (the first $n+1$ terms of a sample path). For $i=1,\dots,n+1$ let
--   $$
--   z_{n,(i)}^*=\min_{x\in X}\frac1n\sum_{\substack{j=1\\ j\ne i}}^{n+1} f(x,\tilde\xi^j)
--   $$
--   be the optimal value of the sample-average problem with the $i$-th observation left out, and assume each of these $n+1$ problems is bounded below on $X$. Then
--   $$
--   \frac1{n+1}\sum_{i=1}^{n+1} z_{n,(i)}^*\ \le\ z_{n+1}^*=\min_{x\in X}\frac1{n+1}\sum_{i=1}^{n+1} f(x,\tilde\xi^i).
--   $$
--
--   This is the deterministic content of the first two steps of the proof of Theorem 2: the $(n+1)$-sample objective is the average of the $n+1$ leave-one-out objectives, and the minimum of an average is at least the average of the minima. Taking expectations gives the inequality of the proof, $Ez_{n+1}^*\ge\frac1{n+1}\sum_i E z_{n,(i)}^*$.
--
--   **Formalization Note.** The statement is pathwise; the paper's display carries an outer expectation, which is added in the milestone on Theorem 2. Indices are 0-based: the left-out index runs over $\{0,\dots,n\}$ and the remaining draws are listed by `skipIndex`. Minima are infima (`sInf`); the boundedness hypotheses are exactly what the infima need to be genuine.
-- source:
--   Mak, Morton & Wood, Oper. Res. Lett. 24 (1999), p. 50, proof of Theorem 2 (first equality and the inequality)

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting
import Definitions.Def_MonteCarloBound_LowerBound_Setting

namespace MonteCarloBound.LowerBound

open MeasureTheory ProbabilityTheory SolutionQuality.SRP

/-- Proof of Theorem 2 (p. 50), pathwise: the minimum of the average of the `n + 1`
leave-one-out objectives is at least the average of their minima. -/
theorem theorem2_loo_pointwise {d : ℕ} {Ξ : Type*}
    (f : E d → Ξ → ℝ) (X : Set (E d)) (hX : X.Nonempty)
    (s : ℕ → Ξ) (n : ℕ) (hn : 1 ≤ n)
    (hbdd : ∀ i ≤ n,
      BddBelow ((fun x => sampleMean f (fun j => s (skipIndex i j)) n x) '' X)) :
    (1 / ((n : ℝ) + 1)) * ∑ i ∈ Finset.range (n + 1), looValue f X s n i ≤
      saaValue f X s (n + 1) := by sorry

end MonteCarloBound.LowerBound
