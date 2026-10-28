-- Prove2me | Theorems.Thm_OTSensitivity_Info_theorem_9
-- name    : OTSensitivity.Info.theorem_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:07.367771+00:00
-- url     : https://prove2.me/theorems/d5ad965f-ffea-4c36-82f1-6537d5b91a76
-- title:
--   Theorem 9 — ξ^K(Y, X|𝓕ⁿ) → ξ^K(Y, X|𝓕) along increasing σ-algebras
-- statement:
--   Let $(\Omega,\mathcal B,\mathbb P)$ be a probability space, $\mathsf X,\mathsf Y$ Polish spaces, $X:\Omega\to\mathsf X$ and $Y:\Omega\to\mathsf Y$ measurable, and $\mathsf k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ continuous with $\mathsf k(y,y')=0\iff y=y'$, with optimal-transport cost $K$ as in (1). Let $(\mathcal F^n)_n$ be an increasing sequence of sub-σ-algebras of $\mathscr B(\mathsf X)$, and $\mathcal F=\bigvee_{n}\mathcal F^n$ the smallest σ-algebra containing each $\mathcal F^n$. Then
--   $$\lim_{n\to\infty}\xi^K(Y,X\mid\mathcal F^n)=\xi^K(Y,X\mid\mathcal F)$$
--   in $[0,+\infty]$, where each $\xi^K(Y,X\mid\mathcal F^n)$ and $\xi^K(Y,X\mid\mathcal F)$ is computed with an arbitrary version of the corresponding conditional distribution.
--
--   Collecting information on $X$ through progressively finer σ-algebras makes the OT-based sensitivity measure converge to its value for the limiting information. The paper uses this for the consistency of its partition estimator (Section 4, Theorem 21).
--
--   **Formalization Note** The paper says "sub-σ-algebras in $\mathcal F$", which is circular as $\mathcal F$ is defined afterwards as their join; it is read as sub-σ-algebras of $\mathscr B(\mathsf X)$, the reading of the sentence before Theorem 9 ("an increasing family of σ-algebras in $\mathscr B(\mathsf X)$"). The sequence is indexed from $0$ instead of $1$, which does not affect the limit. $\mathsf X$ and $\mathsf Y$ are Polish (the paper's supports in $\mathbb R^{n_X}$, $\mathbb R^{n_Y}$ are such spaces). The limit is a `Tendsto` in `ℝ≥0∞`; no finiteness of $\mathbb M^K[Y]$ is assumed, as on the page, and $+\infty$ limits are allowed. Conditional distributions are characterized, not chosen, and the statement holds for every choice of versions, not necessarily compatible across $n$. $K$ is the platform definition `RWPI.SqrtLasso.transportCost`.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Theorem 9 (25), p. 11

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace OTSensitivity.Info

/-- Theorem 9, (25), p. 11: for an increasing sequence `(𝓕ₙ)` of sub-σ-algebras of `𝓑(𝓧)` with
join `𝓕 = ⋁ₙ 𝓕ₙ`, `ξ^K(Y, X | 𝓕ₙ) → ξ^K(Y, X | 𝓕)` in `[0, +∞]`, for every choice of versions of
the conditional distributions. -/
theorem theorem_9 {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω] (Fs : ℕ → MeasurableSpace 𝓧)
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (hmono : Monotone Fs) (hle : ∀ n, Fs n ≤ m𝓧)
    (κs : ℕ → Kernel 𝓧 𝓨) (hκs : ∀ n, IsCondDistrib P X Y (Fs n) (κs n))
    (κ : Kernel 𝓧 𝓨) (hκ : IsCondDistrib P X Y (⨆ n, Fs n) κ) :
    Tendsto (fun n => OTSensitivity.MaxFun.xi k P X Y (κs n)) atTop (𝓝 (OTSensitivity.MaxFun.xi k P X Y κ)) := by sorry

end OTSensitivity.Info
