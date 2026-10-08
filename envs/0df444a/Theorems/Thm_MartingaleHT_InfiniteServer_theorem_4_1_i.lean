-- Prove2me | Theorems.Thm_MartingaleHT_InfiniteServer_theorem_4_1_i
-- name    : MartingaleHT.InfiniteServer.theorem_4_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:10.371161+00:00
-- url     : https://prove2.me/theorems/d4efc3ed-783d-46af-86b1-8a1d96ed11df
-- title:
--   Theorem 4.1(i) — the integral representation $x=b+y+\int_0^\cdot h(x)$ has a unique solution in $D$, continuous in $(y,b)$ for u.o.c. convergence
-- statement:
--   Let $h:\mathbb R\to\mathbb R$ satisfy $h(0)=0$ and the Lipschitz condition (62): there is $c>0$ with $|h(s_1)-h(s_2)|\le c|s_1-s_2|$ for all $s_1,s_2$. Consider
--   $$
--   x(t)=b+y(t)+\int_0^th(x(s))\,ds,\qquad t\ge0. \tag{63}
--   $$
--   1. For every $y\in D$ (right-continuous with left limits) and $b\in\mathbb R$, (63) has a solution $x\in D$, and any two solutions in $D$ agree on $[0,\infty)$.
--   2. If $y$ is continuous on $[0,\infty)$, so is the solution.
--   3. The solution map $f:(y,b)\mapsto x$ is continuous when $D$ carries the topology of uniform convergence on bounded intervals: if $b_n\to b$ and $y_n\to y$ uniformly on $[0,T]$ for every $T\ge0$, then the solutions $x_n\to x$ uniformly on $[0,T]$ for every $T\ge0$.
--
--   With $h(s)=-\mu s$ this turns the martingale representation (32) into a continuous function of the martingales and the initial value.
--
--   **Formalization Note** Only part (i), the topology of uniform convergence over bounded intervals, is formalized; part (ii), the Skorohod $J_1$ topology, needs a $J_1$ notion on $D[0,\infty)$ that the mission does not define. Continuity is stated sequentially, which suffices because that topology is metrizable.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 225, Theorem 4.1 (part (i)), (62)–(63)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_InfiniteServer_Model
import Definitions.Def_MartingaleHT_InfiniteServer_Toolkit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MartingaleHT.InfiniteServer

open BellWilliams2001.ThresholdPolicy ManyServerQED.Scheduling ErlangA.Diffusion

/-- **Theorem 4.1, part (i)** (continuity of the integral representation, p. 225). Let
`h : ℝ → ℝ` satisfy `h(0) = 0` and the Lipschitz condition (62) with a constant `c > 0`. Then:
1. for every `y ∈ D` and `b ∈ ℝ` the integral representation (63),
   `x(t) = b + y(t) + ∫₀ᵗ h(x(s)) ds`, `t ≥ 0`, has a solution `x ∈ D`, and any two solutions in
   `D` agree on `[0, ∞)`;
2. if `y` is continuous on `[0, ∞)`, so is the solution;
3. the solution map `(y, b) ↦ x` is continuous for the topology of uniform convergence on
   bounded intervals: if `bₙ → b` and `yₙ → y` uniformly on `[0, T]` for every `T`, then the
   solutions `xₙ → x` uniformly on `[0, T]` for every `T`. -/
theorem theorem_4_1_i (h : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hLip : ∀ s₁ s₂ : ℝ, |h s₁ - h s₂| ≤ c * |s₁ - s₂|) (h0 : h 0 = 0) :
    (∀ (y : ℝ → ℝ) (b : ℝ), IsCadlag y →
      (∃ x : ℝ → ℝ, SolvesIntegralRep h b y x) ∧
      (∀ x₁ x₂ : ℝ → ℝ, SolvesIntegralRep h b y x₁ → SolvesIntegralRep h b y x₂ →
        ∀ t : ℝ, 0 ≤ t → x₁ t = x₂ t) ∧
      (ContinuousOn y (Set.Ici 0) → ∀ x : ℝ → ℝ, SolvesIntegralRep h b y x →
        ContinuousOn x (Set.Ici 0))) ∧
    ∀ (yn : ℕ → ℝ → ℝ) (bn : ℕ → ℝ) (xn : ℕ → ℝ → ℝ) (y : ℝ → ℝ) (b : ℝ) (x : ℝ → ℝ),
      (∀ n, IsCadlag (yn n)) → IsCadlag y →
      (∀ n, SolvesIntegralRep h (bn n) (yn n) (xn n)) → SolvesIntegralRep h b y x →
      Tendsto bn atTop (𝓝 b) →
      (∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn yn y atTop (Set.Icc 0 T)) →
      ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn xn x atTop (Set.Icc 0 T) := by sorry

end MartingaleHT.InfiniteServer
