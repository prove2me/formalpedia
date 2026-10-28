-- Prove2me | Theorems.Thm_OTSensitivity_Info_theorem_8_i
-- name    : OTSensitivity.Info.theorem_8_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:53.299826+00:00
-- url     : https://prove2.me/theorems/4b82f022-94f3-43b2-a798-dcfec517682e
-- title:
--   Theorem 8 (23) — ξ^K(Y, X) ≥ ξ^K(Y, X|𝓕) for every 𝓕 ⊂ 𝓑(𝖷)
-- statement:
--   Let $(\Omega,\mathcal B,\mathbb P)$ be a probability space, $\mathsf X,\mathsf Y$ Polish spaces, $X:\Omega\to\mathsf X$ and $Y:\Omega\to\mathsf Y$ measurable, and $\mathsf k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ continuous with $\mathsf k(y,y')=0\iff y=y'$. For every σ-algebra $\mathcal F\subseteq\mathscr B(\mathsf X)$,
--   $$\xi^K(Y,X)\ \ge\ \xi^K(Y,X\mid\mathcal F),$$
--   where $\xi^K(Y,X)$ is computed with any version of the conditional distribution of $Y$ given $X$ and $\xi^K(Y,X\mid\mathcal F)$ with any version of the conditional distribution of $Y$ given $(X,\mathcal F)$.
--
--   Coarser information on $X$ never increases the OT-based sensitivity measure: full information on $X$ is the most valuable.
--
--   **Formalization Note** $\mathsf X$ and $\mathsf Y$ are Polish (the paper's supports in $\mathbb R^{n_X}$, $\mathbb R^{n_Y}$ are such spaces). Values are in $[0,+\infty]$, so the inequality holds also when either side is infinite. The statement holds for every pair of versions of the conditional distributions. $K$ is the platform definition `RWPI.SqrtLasso.transportCost`.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Theorem 8 (23), p. 11

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace OTSensitivity.Info

/-- Theorem 8, (23), p. 11: for every σ-algebra `𝓕 ⊂ 𝓑(𝓧)`, `ξ^K(Y, X) ≥ ξ^K(Y, X | 𝓕)`. -/
theorem theorem_8_i {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω] (F : MeasurableSpace 𝓧)
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (hF : F ≤ m𝓧)
    (κ : Kernel 𝓧 𝓨) (hκ : IsCondDistrib P X Y m𝓧 κ)
    (κF : Kernel 𝓧 𝓨) (hκF : IsCondDistrib P X Y F κF) :
    OTSensitivity.MaxFun.xi k P X Y κF ≤ OTSensitivity.MaxFun.xi k P X Y κ := by sorry

end OTSensitivity.Info
