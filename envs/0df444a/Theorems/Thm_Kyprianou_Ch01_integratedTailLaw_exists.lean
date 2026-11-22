-- Prove2me | Theorems.Thm_Kyprianou_Ch01_integratedTailLaw_exists
-- name    : Kyprianou.Ch01.integratedTailLaw_exists
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-21T09:19:38.60714+00:00
-- url     : https://prove2.me/theorems/f9c4bbde-14b6-4528-ade1-a77bce82b13a
-- title:
--   Integrated-tail (equilibrium) law of a positive claim distribution exists
-- statement:
--   Let $F$ be a probability law on $(0,\infty)$ (i.e. $F((-\infty,0])=0$) with finite mean $\mu=\int x\,F(dx)>0$. Then there is a probability measure $\eta$ on $\mathbb R$, carried by $[0,\infty)$, whose distribution function is the normalised integrated tail of $F$:
--
--   $$\eta([0,x]) \;=\; \frac{1}{\mu}\int_0^x F\big((y,\infty)\big)\,dy, \qquad x\ge 0.$$
--
--   Concretely $\eta(dy)=\mu^{-1}\,\overline F(y)\,\mathbf 1_{\{y>0\}}\,dy$; the total mass is one because $\int_0^\infty \overline F(y)\,dy=\mu$ (layer-cake formula). This is the law of the deficit at first ruin in Theorem 1.9 and the summand law of the Pollaczek–Khintchine series.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, §1.3.1, Theorems 1.8–1.10, pp. 15–18 (integrated-tail distribution appearing in Theorems 1.8 and 1.9)

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.integratedTailLaw_exists
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu) :
    ∃ eta : Measure ℝ, IsProbabilityMeasure eta ∧
      eta (Set.Iio (0 : ℝ)) = 0 ∧
      ∀ x : ℝ, 0 ≤ x →
        (eta (Set.Iic x)).toReal = integratedTailCDF F mu x := by
  sorry
