-- Prove2me | Theorems.Thm_HighMagSampling_SK_lemma_1
-- name    : HighMagSampling.SK.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:27:44.55159+00:00
-- url     : https://prove2.me/theorems/7cc186ae-1dc0-4847-8174-5880de71328e
-- title:
--   Lemma 1 — a $\lambda$-Poincaré inequality gives $\chi^2(\pi_t\|\pi)\le(1-\lambda/2)^t\chi^2(\pi_0\|\pi)$ for the lazy chain
-- statement:
--   Let $\mathcal T$ be a Markov chain (kernel) on a measurable space $\Omega$ that is reversible with stationary probability measure $\pi$, and suppose $\mathcal T$ satisfies a $\lambda$-Poincaré inequality, $\lambda\in(0,2]$. Let $\mathrm{lazy}(\mathcal T)$ step according to $\mathcal T$ with probability $\tfrac12$ and otherwise stay, and let $\pi_t$ be the law after $t\in\mathbb N$ steps of $\mathrm{lazy}(\mathcal T)$ from a probability measure $\pi_0$. Then
--   $$\chi^2(\pi_t\|\pi)\ \le\ \Big(1-\frac\lambda2\Big)^t\,\chi^2(\pi_0\|\pi).$$
--
--   This is the step (from Levin–Peres–Wilmer, Chapters 12–13) that turns the Poincaré inequality of the down-up walk into geometric convergence; combined with the comparison inequality it bounds the total-variation mixing time.
--
--   **Formalization Note.** $\chi^2$ is `PolySampIso.chiSq` ($[0,\infty]$-valued) and the factor $(1-\lambda/2)^t\ge0$ enters through `ENNReal.ofReal`. The Poincaré inequality is the mission's `SatisfiesPoincare` (over $f\in L^2(\pi)$, with $\lambda\in(0,2]$).
--
--   Differences from the source:
--   - reading: densities on a general $\Omega$ and "all $f$" with footnote 4 → $\chi^2$ through the Radon–Nikodym derivative ($+\infty$ off absolute continuity) and the Poincaré inequality over $f\in L^2(\pi)$; reason: the paper's general-$\Omega$ formulas and its footnote 4, which restricts to functions for which the integrals make sense.
--   - encoding: no assumption on $\chi^2(\pi_0\|\pi)$ → hypothesis $\chi^2(\pi_0\|\pi)<\infty$; reason: when $\chi^2(\pi_0\|\pi)=\infty$ the printed right-hand side is $+\infty$ (no content) or, at $\lambda=2$, the undefined product $0\cdot\infty$, which $[0,\infty]$ arithmetic would set to $0$.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 11, Lemma 1

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_HighMagSampling_SK_MarkovChain

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HighMagSampling.SK

/-- Lemma 1, p. 11: if a reversible Markov kernel `κ` with stationary measure `π` satisfies a
`λ`-Poincaré inequality, the law `π_t` after `t` steps of `lazy κ` from `π₀` satisfies
`χ²(π_t ‖ π) ≤ (1 − λ/2)^t χ²(π₀ ‖ π)`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : Measure Ω) [IsProbabilityMeasure π] (hrev : IsReversibleWith κ π) (lam : ℝ)
    (hP : SatisfiesPoincare κ π lam) (π₀ : Measure Ω) [IsProbabilityMeasure π₀]
    (hfin : PolySampIso.chiSq π₀ π ≠ ⊤) (t : ℕ) :
    PolySampIso.chiSq (lawAfter (lazy κ) π₀ t) π ≤
      ENNReal.ofReal ((1 - lam / 2) ^ t) * PolySampIso.chiSq π₀ π := by sorry

end HighMagSampling.SK
