-- Prove2me | Theorems.Thm_MonteCarloBound_LowerBound_theorem2_monotone
-- name    : MonteCarloBound.LowerBound.theorem2_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:09.463607+00:00
-- url     : https://prove2.me/theorems/b8a9c427-e630-4b31-ab2a-64f357002302
-- title:
--   Theorem 2, p. 50 — E z*_{n+1} ≥ E z*_n
-- statement:
--   Let $X\subseteq\mathbb R^d$, let $f$ be real valued, and let $\tilde\xi^1,\dots,\tilde\xi^n,\tilde\xi^{n+1}$, $n\ge1$, be i.i.d. from the distribution of $\tilde\xi$, used to define both
--   $$
--   z_n^*=\min_{x\in X}\frac1n\sum_{i=1}^n f(x,\tilde\xi^i)\quad\text{and}\quad z_{n+1}^*=\min_{x\in X}\frac1{n+1}\sum_{i=1}^{n+1} f(x,\tilde\xi^i).
--   $$
--   Assume that, with probability one, every sample-average problem $\mathrm{SP}_m$, $m\ge1$, has an optimal solution $x_m^*$, that $z_n^*$ is a random variable (measurable as a function of the sample path), and that $Ez_n^*$ and $Ez_{n+1}^*$ exist. Then
--   $$
--   Ez_{n+1}^*\ \ge\ Ez_n^*.
--   $$
--
--   Together with Theorem 1, this says that the lower bound $Ez_n^*$ on $z^*$ improves monotonically, in expectation, as the sample size grows.
--
--   **Formalization Note.** Both optimal values use the same sequence `ξ 0, ξ 1, …` (common random numbers, as in the theorem's statement): $z_n^*$ uses its first $n$ terms, $z_{n+1}^*$ its first $n+1$. The attainment hypothesis is stated almost surely with respect to the law of the sample path; this is the paper's "$x_m^*\in\arg\min$" and it keeps the infima (`sInf`) genuine. The integrability hypotheses make "$Ez_n^*$ exists" precise; without them the Lean integral would default to $0$. The theorem does not use the existence of $Ef(x,\tilde\xi)$ or of an optimal solution of $\mathrm{SP}$, so those hypotheses are omitted, which makes the statement stronger.
-- source:
--   Mak, Morton & Wood, Oper. Res. Lett. 24 (1999), p. 50, Theorem 2

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting
import Definitions.Def_MonteCarloBound_LowerBound_Setting

namespace MonteCarloBound.LowerBound

open MeasureTheory ProbabilityTheory SolutionQuality.SRP

/-- Theorem 2 (p. 50): `E z*_{n+1} ≥ E z*_n`, with `z*_n` and `z*_{n+1}` built on the same
i.i.d. sequence. -/
theorem theorem2_monotone {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (X : Set (E d))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (n : ℕ) (hn : 1 ≤ n)
    (hmin : ∀ᵐ s ∂(pathLaw P ξ), ∀ m, 1 ≤ m →
      ∃ x ∈ X, ∀ y ∈ X, sampleMean f s m x ≤ sampleMean f s m y)
    (hzint : Integrable (fun ω => saaValue f X (fun i => ξ i ω) n) P)
    (hzint1 : Integrable (fun ω => saaValue f X (fun i => ξ i ω) (n + 1)) P)
    (hzmeas : Measurable (fun s : ℕ → Ξ => saaValue f X s n)) :
    ∫ ω, saaValue f X (fun i => ξ i ω) n ∂P ≤ ∫ ω, saaValue f X (fun i => ξ i ω) (n + 1) ∂P := by sorry

end MonteCarloBound.LowerBound
