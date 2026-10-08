-- Prove2me | Theorems.Thm_KingmanSubadditive_Ergodic_fekete
-- name    : KingmanSubadditive.Ergodic.fekete
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:41:46.875985+00:00
-- url     : https://prove2.me/theorems/33293703-2487-4c4b-83ed-b928a03dca38
-- title:
--   (1.1.4)–(1.1.5): the means converge to γ
-- statement:
--   Let $(x_{st})_{s<t}$ be random variables on a probability space satisfying S₁ ($x_{su}\le x_{st}+x_{tu}$ for $s<t<u$), S₂′ (the distribution of $x_{st}$ depends only on $t-s$) and S₃ (each $x_{0t}$, $t\ge1$, is integrable and $g_t=E_P(x_{0t})\ge-At$ for some constant $A$). Write $\gamma(x)=\inf_{u\ge1}g_u/u$. Then
--   $$\lim_{t\to\infty}\frac{g_t}{t}=\gamma(x).$$
--   The linear lower bound in S₃ makes $\gamma(x)$ finite. This identifies the mean growth rate that appears in Theorem 1.
--
--   **Formalization Note** The infimum ranges over positive times only. Only the one-dimensional stationarity S₂′ is assumed, as on the page, written as equality of the law of $x_{st}$ with the law of $x_{0,t-s}$ for every $s<t$; the joint-law condition S₂ of a subadditive process is not needed.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 883, (1.1.4)–(1.1.5)

import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process

namespace KingmanSubadditive.Ergodic

open MeasureTheory Filter Topology

/-- Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973),
p. 883, (1.1.4)–(1.1.5). As on the page, the hypotheses are S₁, S₃ and only
the one-dimensional stationarity S₂′ ("the distribution of `x_st` depends only
on `t − s`"), written as equality of the law of `x_st` with that of
`x_{0,t−s}` for every `s < t` (the natural-number subtraction is never
truncated there). Measurability of each valid coordinate is the paper's
"random variables". The infimum `gamma` excludes `t = 0`. -/
theorem fekete {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ s t : ℕ, s < t → Measurable (x s t))
    (hS1 : S1 x)
    (hS2' : ∀ s t : ℕ, s < t → Measure.map (x s t) P = Measure.map (x 0 (t - s)) P)
    (hS3 : S3 P x) :
    Tendsto (fun t : ℕ => mean P x t / (t : ℝ)) atTop (𝓝 (gamma P x)) := by sorry

end KingmanSubadditive.Ergodic
