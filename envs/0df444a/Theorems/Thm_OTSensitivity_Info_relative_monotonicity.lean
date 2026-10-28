-- Prove2me | Theorems.Thm_OTSensitivity_Info_relative_monotonicity
-- name    : OTSensitivity.Info.relative_monotonicity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:06.152855+00:00
-- url     : https://prove2.me/theorems/bf2e4040-a86c-480d-99f7-40051145542e
-- title:
--   Theorem 8 relative to 𝓕 — ξ^K(Y, X|𝓖) ≤ ξ^K(Y, X|𝓕) for 𝓖 ⊆ 𝓕 ⊆ 𝓑(𝖷)
-- statement:
--   Let $(\Omega,\mathcal B,\mathbb P)$ be a probability space, $\mathsf X,\mathsf Y$ Polish spaces, $X:\Omega\to\mathsf X$ and $Y:\Omega\to\mathsf Y$ measurable, and $\mathsf k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ continuous with $\mathsf k(y,y')=0\iff y=y'$. If $\mathcal G\subseteq\mathcal F\subseteq\mathscr B(\mathsf X)$ are σ-algebras, then
--   $$\xi^K(Y,X\mid\mathcal G)\ \le\ \xi^K(Y,X\mid\mathcal F),$$
--   for any versions of the conditional distributions of $Y$ given $(X,\mathcal G)$ and given $(X,\mathcal F)$.
--
--   The paper uses this form after Theorem 9 ("by Theorem 8, $\xi^K(Y,X\mid\mathcal F^n)$ is smaller than $\xi(Y,X\mid\mathcal F)$") and in the first line of its proof ($\limsup_n\xi^K(Y,X\mid\mathcal F_n)\le\xi^K(Y,X\mid\mathcal F)$).
--
--   **Formalization Note** Theorem 8 as printed compares $\xi^K(Y,X\mid\mathcal F)$ only with $\xi^K(Y,X)$, i.e. $\mathcal F$ against $\mathscr B(\mathsf X)$; the comparison of two sub-σ-algebras used for Theorem 9 is posed here as its own statement (a disclosed correction). With $\mathcal F=\mathscr B(\mathsf X)$ it is (23).
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), discussion after Theorem 9, p. 11; Appendix A, proof of Theorem 9, first sentence, p. 36

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace OTSensitivity.Info

/-- Discussion after Theorem 9, p. 11, and proof of Theorem 9, p. 36 (Theorem 8 relative to a
σ-algebra `𝓕`): if `𝓖 ⊆ 𝓕 ⊆ 𝓑(𝓧)` then `ξ^K(Y, X | 𝓖) ≤ ξ^K(Y, X | 𝓕)`. -/
theorem relative_monotonicity {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω] (G F : MeasurableSpace 𝓧)
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (hGF : G ≤ F) (hF : F ≤ m𝓧)
    (κG : Kernel 𝓧 𝓨) (hκG : IsCondDistrib P X Y G κG)
    (κF : Kernel 𝓧 𝓨) (hκF : IsCondDistrib P X Y F κF) :
    OTSensitivity.MaxFun.xi k P X Y κG ≤ OTSensitivity.MaxFun.xi k P X Y κF := by sorry

end OTSensitivity.Info
