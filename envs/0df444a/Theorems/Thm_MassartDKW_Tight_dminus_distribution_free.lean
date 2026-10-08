-- Prove2me | Theorems.Thm_MassartDKW_Tight_dminus_distribution_free
-- name    : MassartDKW.Tight.dminus_distribution_free
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:57:22.234499+00:00
-- url     : https://prove2.me/theorems/dfabb64b-27ce-495c-b72c-2190820ebb06
-- title:
--   §2, p. 1271, first sentence — the law of Dₙ⁻ is the same for all continuous F
-- statement:
--   Let $n\ge1$. Let $x_1,\dots,x_n$ be i.i.d. real random variables on $(\Omega,P)$ with a law $\mu$ whose distribution function $F$ is continuous, and let $y_1,\dots,y_n$ be i.i.d. real random variables on $(\Omega',P')$ with a law $\nu$ whose distribution function $G$ is continuous. Write $D_n^-(x)$ and $D_n^-(y)$ for the statistics $\sqrt n\sup_x(F-\hat F_n)$ of the two samples (each computed with its own distribution function). Then for every real $\lambda$,
--   $$P\bigl(D_n^-(x)>\lambda\bigr)=P'\bigl(D_n^-(y)>\lambda\bigr).$$
--
--   This is the reduction with which the proof of Theorem 1 opens: the distribution of $D_n^-$ does not depend on the continuous law $F$, so one may take $F$ uniform on $[0,1]$.
--
--   **Formalization Note** The page states this for $D_n$; the proof uses it for $D_n^-$, which is what is stated here. Equality in law is stated through the tail probabilities $P(D_n^->\lambda)$ for every $\lambda$, which determine the law, rather than as an equality of image measures (an image measure under a map not proven measurable is the zero measure in Mathlib, which would make that form vacuous). Independence is `iIndepFun`, identical distribution is `HasLaw (X i) μ P` for every $i$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1271, §2, first sentence

import Mathlib
import Definitions.Def_MassartDKW_Tight_EmpiricalProcess
open MeasureTheory ProbabilityTheory

namespace MassartDKW.Tight

theorem dminus_distribution_free {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (n : ℕ) (hn : 1 ≤ n) (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hFμ : Continuous (cdf μ)) (hFν : Continuous (cdf ν))
    (X : Fin n → Ω → ℝ) (hlawX : ∀ i, HasLaw (X i) μ P) (hindX : iIndepFun X P)
    (Y : Fin n → Ω' → ℝ) (hlawY : ∀ i, HasLaw (Y i) ν P') (hindY : iIndepFun Y P') :
    ∀ l : ℝ, P {ω | l < Dminus μ X ω} = P' {ω | l < Dminus ν Y ω} := by sorry

end MassartDKW.Tight
