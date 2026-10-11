-- Prove2me | Theorems.Thm_KPZBallistic_random_deposition_clt
-- name    : KPZBallistic.random_deposition_clt
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:28:12.105107+00:00
-- url     : https://prove2.me/theorems/057a09d5-8c25-44ed-8473-e12ac328b684
-- title:
--   Random deposition: $(N_t-t)/\sqrt t\Rightarrow\mathcal N(0,1)$
-- statement:
--   Let $N_t(0)$ be the random deposition height of column $0$ at time $t$, i.e. the number of rings of a rate-one Poisson clock in $[0,t]$. For every $x\in\mathbb R$,
--
--   $$
--   \lim_{t\to\infty}P\Big(\frac{N_t(0)-t}{\sqrt t}\le x\Big)=\Phi(x),
--   $$
--
--   where $\Phi$ is the standard Gaussian distribution function. Random deposition has no spatial interaction and is in the Gaussian universality class (fluctuation exponent $1/2$); it is the baseline against which KPZ behaviour is contrasted.
-- source:
--   I. Corwin, The Kardar-Parisi-Zhang equation and universality class, Random Matrices Theory Appl. 1 (2012), https://arxiv.org/abs/1106.1596, Section 1.1.1, p. 3 (random deposition: 'the height at time t fluctuates like t^{1/2} and is governed by the Gaussian distribution (due to the classical central limit theorem)'); Open Problem Garden, 'KPZ Universality Conjecture' (posted by T. Kojar, 2020), http://www.openproblemgarden.org/op/kpz_universality_conjecture

import Mathlib
import Definitions.Def_KPZBallistic_Defs

open MeasureTheory ProbabilityTheory Filter Topology

namespace KPZBallistic

theorem random_deposition_clt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℤ → ℕ → Ω → ℝ) (hτ : IsPoissonClocks P τ) (x : ℝ) :
    Tendsto (fun t : ℝ => P.real {ω | ((rdHeight τ t 0 ω : ℝ) - t) / Real.sqrt t ≤ x})
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic x))) := by sorry

end KPZBallistic
