-- Prove2me | Theorems.Thm_LearnStability_Characterization_utility_lemma12
-- name    : LearnStability.Characterization.utility_lemma12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:08:30.429335+00:00
-- url     : https://prove2.me/theorems/1f0a04d0-4ae6-4689-b376-71726d4e7bb1
-- title:
--   Utility Lemma 12 — the sample mean of a bounded variable deviates by at most B/√m in expectation
-- statement:
--   Let $\mathcal D$ be a probability distribution on $\mathcal Z$ and $g:\mathcal Z\to\mathbb R$ a measurable function with $|g(z)|\le B$ for all $z$. For $m\ge1$ let $S=(z_1,\dots,z_m)\sim\mathcal D^m$ and $X=\frac1m\sum_{i=1}^m g(z_i)$, so that $\mathbb E[X]=\mathbb E_{z\sim\mathcal D}[g(z)]$. Then
--   $$\mathbb E\bigl[|X-\mathbb E[X]|\bigr]\le\frac{B}{\sqrt m}.$$
--
--   This is the only concentration fact used in the converse direction of Theorem 7 (Lemmas 16 and 20), where $g=f(h;\cdot)$ for a fixed hypothesis $h$.
--
--   **Formalization Note.** The paper states the lemma for i.i.d. real variables $X_i$ with $|X_i|\le B$. It is stated here for $X_i=g(z_i)$, which is how the paper uses it; the two forms are equivalent (take $\mathcal Z=\mathbb R$, $\mathcal D$ the common law, and $g$ the identity clipped to $[-B,B]$).
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2650, Utility Lemma 12

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting

open MeasureTheory

namespace LearnStability.Characterization

/-- Utility Lemma 12 (p. 2650), for the sample average of a bounded measurable function:
if `|g(z)| ≤ B` for all `z` and `S = (z_1, …, z_m) ∼ D^m` with `m ≥ 1`, then
`E[|(1/m) ∑_i g(z_i) − E_D[g]|] ≤ B / √m`. -/
theorem utility_lemma12 {Z : Type*} [MeasurableSpace Z]
    (D : Measure Z) [IsProbabilityMeasure D]
    (g : Z → ℝ) (B : ℝ) (hg : Measurable g) (hB : ∀ z, |g z| ≤ B)
    (m : ℕ) (hm : 1 ≤ m) :
    ∫ S, |(∑ i, g (S i)) / m - ∫ z, g z ∂D| ∂(sampleLaw D m) ≤ B / Real.sqrt m := by sorry

end LearnStability.Characterization
