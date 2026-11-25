-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_centered_poisson_scaled_sup_moment
-- name    : ManyServerQED.Scheduling.centered_poisson_scaled_sup_moment
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T19:48:34.202379+00:00
-- url     : https://prove2.me/theorems/42ab9f54-dd82-492c-85ea-07b3d2587da4
-- title:
--   Uniform moment bound for a diffusion-scaled Poisson maximum
-- statement:
--   Let $N$ be a Poisson counting process of rate $a$ and let $A\ge a$ be a deterministic rate bound. For every real $p>1$, positive integer $n$, and $T\ge0$,
--   $$\mathbb E\left[\sup_{0\le t\le T}\left|\frac{N(nt)-a n t}{\sqrt n}\right|^p\right]\le C_{p,A}(1+T)^p.$$
--   The constant is uniform in $n$ and in the Poisson rate under the bound $A$. The estimate supplies the Poisson fluctuation bounds used for service and abandonment in the work-conserving queue moment argument.
-- source:
--   Auxiliary Poisson moment estimate for Atar, Mandelbaum and Reiman, https://arxiv.org/pdf/math/0407058, proof of Lemma 3 (p. 32), service and abandonment noise

import Definitions.Def_ManyServerQED_Scheduling_Model
open MeasureTheory Set
open scoped ENNReal

theorem ManyServerQED.Scheduling.centered_poisson_scaled_sup_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : Ω → ℝ → ℝ} {a : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N a) (p A : ℝ) (hp : 1 < p)
    (hA : a ≤ A) (n : ℕ) (hn : 1 ≤ n) (T : ℝ) (hT : 0 ≤ T) :
    let C := (2 : ℝ)^p * (((p/(p-1))^p) * (2 * (⌈p⌉₊.factorial : ℝ) * Real.exp A) + A^p)
    ∫⁻ ω, (⨆ t : ℝ, ⨆ (_ : t ∈ Icc 0 T),
      ENNReal.ofReal |(N ω ((n : ℝ)*t) - a*(n : ℝ)*t) / Real.sqrt n|)^p ∂P ≤
      ENNReal.ofReal (C * (1+T)^p) := by sorry
