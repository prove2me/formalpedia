-- Prove2me | Theorems.Thm_OAI_RandomKSAT_pathReward_sq_potential
-- name    : OAI.RandomKSAT.pathReward_sq_potential
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:05:56.754796+00:00
-- url     : https://prove2.me/theorems/898f4fe2-210a-4ec6-915b-68788fb97624
-- title:
--   Second-moment bound for path rewards from a potential function
-- statement:
--   Let $X$ be a set (the state space) and $\alpha$ a finite nonempty set (the noise space), and let $s_i:\alpha\times X\to X$ ($i\in\mathbb N$) be time-dependent transition maps. For a start $x\in X$ and noise $w=(w_0,\dots,w_{m-1})\in\alpha^m$ the path is $x_0=x$, $x_{i+1}=s_i(w_i,x_i)$, and for a reward $f:X\to\mathbb R$ the *path reward* is $R_m(w,x)=\sum_{i=0}^{m-1}f(x_i)$. Let $(U_i\varphi)(x)=\frac1{|\alpha|}\sum_{a\in\alpha}\varphi\big(s_i(a,x)\big)$ be the one-step averaging operators. For a reward $g$ let $\mathcal M_m(g)$ be the cumulative reward defined by $\mathcal M_0(g)=0$ and $\mathcal M_{m+1}(g)=g+U_0\big(\mathcal M_m^{+}(g)\big)$, where $\mathcal M^{+}$ refers to the shifted maps $(s_{i+1})_i$; thus $\mathcal M_m(g)(x)=\mathbb E\sum_{i<m}g(x_i)$ when $w_0,\dots,w_{m-1}$ are independent and uniform on $\alpha$.
--
--   **Theorem.** Let $f,\tau:X\to\mathbb R$ be nonnegative and let $z_i\ge0$ ($i\in\mathbb N$) satisfy the drift condition $f(x)+(U_i\tau)(x)\le\tau(x)+z_i$ for all $i$ and $x$. If $m\in\mathbb N$ and $Z\in\mathbb R$ satisfy $\sum_{i=0}^{m-1}z_i\le Z$, then for every $x\in X$
--   $$
--   \frac1{|\alpha|^m}\sum_{w\in\alpha^m}R_m(w,x)^2\le2\,\mathcal M_m\big(f\,(\tau+Z)\big)(x),
--   $$
--   that is, $\mathbb E\big[\big(\sum_{i<m}f(x_i)\big)^2\big]\le2\,\mathbb E\big[\sum_{i<m}f(x_i)\big(\tau(x_i)+Z\big)\big]$.
--
--   This is the second-moment companion of the potential-function bound for the mean: a nonnegative potential whose expected decrease dominates the reward controls not only the expected total reward, which is at most $\tau(x)+Z$, but also its mean square. It is used to bound second moments of rewards accumulated along random clause processes.
--
--   **Formalization Note** $R_m$ is `pathReward step f m w x`, $U_i$ is `uniformStep step i`, $\mathcal M_m$ is `markovSum (uniformStep step)`, and the average over $w$ is `favg`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FiberRefresh.lean#L251-L298

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.pathReward_sq_potential.{u_1, u_2} {X : Type u_1} {α : Type u_2} [Fintype α] [Nonempty α]
    (step : ℕ → α → X → X) (f τ : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hτ : ∀ x, 0 ≤ τ x) (z : ℕ → ℝ)
    (hz : ∀ i, 0 ≤ z i)
    (hdrift : ∀ i x, f x + uniformStep step i τ x ≤ τ x+z i)
    {Z : ℝ} (m : ℕ) (hZ : (∑ i ∈ Finset.range m, z i) ≤ Z) (x : X) :
    favg (fun w : Fin m → α => (pathReward step f m w x)^2) ≤
      2 * markovSum (uniformStep step) (fun y => f y*(τ y+Z)) m x := by sorry
