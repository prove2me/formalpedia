-- Prove2me | Theorems.Thm_MonteCarloBound_LowerBound_theorem2_loo_expectation
-- name    : MonteCarloBound.LowerBound.theorem2_loo_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:06.365178+00:00
-- url     : https://prove2.me/theorems/20daa2a0-fe33-4ac7-aab4-de344bd5e5e4
-- title:
--   Proof of Theorem 2, p. 50 — each leave-one-out optimal value has expectation E z*_n
-- statement:
--   Let $\tilde\xi^1,\tilde\xi^2,\dots$ be i.i.d. from the distribution $\mu$ of $\tilde\xi$, on a probability space $(\Omega,P)$. Fix $X\subseteq\mathbb R^d$, a real-valued $f$, and a sample size $n$, and assume that the sample-average optimal value $z_n^*$, viewed as a function of the sample path, is measurable. For an index $i$, let
--   $$
--   z_{n,(i)}^*=\min_{x\in X}\frac1n\sum_{\substack{j=1\\ j\ne i}}^{n+1} f(x,\tilde\xi^j)
--   $$
--   be the optimal value of the sample-average problem built on the first $n+1$ observations with the $i$-th one left out. Then
--   $$
--   E\,z_{n,(i)}^*=E z_n^*.
--   $$
--
--   This is the last equality in the proof of Theorem 2: the $n$ observations that remain after one is deleted are again $n$ i.i.d. draws from the distribution of $\tilde\xi$, so the leave-one-out problem has the same law as $\mathrm{SP}_n$.
--
--   **Formalization Note.** The equality is stated for every index $i$ (0-based), not only for $i\le n$; for every $i$ the reindexed sequence is again an i.i.d. sequence with law $\mu$, and the two expectations are integrals of one measurable function of the path against the same law. No integrability is assumed: both sides are Bochner integrals of the same function against the same law, so the identity holds even when they are $0$ by convention. Measurability of $z_n^*$ as a function of the path (on the product $\sigma$-algebra) makes "$z_n^*$ is a random variable" precise; it holds, e.g., for finite or countable $X$, or when $f(\cdot,\xi)$ is continuous on $X$.
-- source:
--   Mak, Morton & Wood, Oper. Res. Lett. 24 (1999), p. 50, proof of Theorem 2 (last equality)

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting
import Definitions.Def_MonteCarloBound_LowerBound_Setting

namespace MonteCarloBound.LowerBound

open MeasureTheory ProbabilityTheory SolutionQuality.SRP

/-- Proof of Theorem 2 (p. 50), last equality: every leave-one-out optimal value has the
same expectation as `z*_n`. -/
theorem theorem2_loo_expectation {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (f : E d → Ξ → ℝ) (X : Set (E d)) (n : ℕ)
    (hzmeas : Measurable (fun s : ℕ → Ξ => saaValue f X s n))
    (i : ℕ) :
    ∫ ω, looValue f X (fun j => ξ j ω) n i ∂P = ∫ ω, saaValue f X (fun j => ξ j ω) n ∂P := by sorry

end MonteCarloBound.LowerBound
