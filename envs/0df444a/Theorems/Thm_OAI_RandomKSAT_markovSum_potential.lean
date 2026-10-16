-- Prove2me | Theorems.Thm_OAI_RandomKSAT_markovSum_potential
-- name    : OAI.RandomKSAT.markovSum_potential
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:02:20.943527+00:00
-- url     : https://prove2.me/theorems/253805c1-f65d-46a7-8214-cf864f1ec04f
-- title:
--   Potential-function bound for cumulative rewards of monotone averaging operators
-- statement:
--   Let $X$ be a set and let $(P_i)_{i\in\mathbb N}$ be maps sending real functions on $X$ to real functions on $X$ such that every $P_i$ is
--
--   - *monotone*: $\varphi\le\psi$ pointwise implies $P_i\varphi\le P_i\psi$ pointwise, and
--   - *compatible with constants*: $P_i(\varphi+c)=P_i\varphi+c$ for every function $\varphi$ and every constant $c\in\mathbb R$.
--
--   For a reward $f:X\to\mathbb R$ the cumulative rewards $M_m(P,f):X\to\mathbb R$ are defined recursively by $M_0(P,f)=0$ and $M_{m+1}(P,f)(x)=f(x)+P_0\big(M_m(P^{+},f)\big)(x)$, where $P^{+}=(P_{i+1})_{i\in\mathbb N}$ is the shifted sequence. Thus $M_m(P,f)=f+P_0\big(f+P_1(f+\dots+P_{m-1}(0))\big)$; when $P_i$ is the one-step expectation operator of a Markov chain at time $i$, $M_m(P,f)(x)$ is the expected total reward $\mathbb E_x\sum_{i<m}f(X_i)$.
--
--   **Theorem.** Let $f,\tau:X\to\mathbb R$ with $\tau\ge0$, and let $(z_i)_{i\in\mathbb N}$ be real numbers such that the drift condition
--   $$
--   f(x)+(P_i\tau)(x)\le\tau(x)+z_i\qquad\text{for all } i\in\mathbb N,\ x\in X
--   $$
--   holds. Then for every $m\in\mathbb N$ and every $x\in X$,
--   $$
--   M_m(P,f)(x)\le\tau(x)+\sum_{i=0}^{m-1}z_i .
--   $$
--
--   This is the potential-function (drift) method: if a nonnegative potential decreases in expectation by at least the collected reward, up to a slack $z_i$ at step $i$, then the initial potential plus the total slack bounds the total expected reward. In the analysis of random $k$-SAT the potential is the expected lifetime of a solution set under random clauses.
--
--   **Formalization Note** $M_m(P,f)$ is `markovSum P f m`. The operators are arbitrary maps `(X → ℝ) → X → ℝ`; no linearity is assumed, and $P_i(0)$ need not vanish.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/LifetimePotential.lean#L56-L74

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.markovSum_potential.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ)
    (hP : ∀ i, Monotone (P i))
    (hPc : ∀ i f c, P i (fun x => f x+c) = fun x => P i f x+c)
    (f τ : X → ℝ) (hτ : ∀ x, 0 ≤ τ x) (z : ℕ → ℝ)
    (hdrift : ∀ i x, f x + P i τ x ≤ τ x + z i) (m : ℕ) (x : X) :
    markovSum P f m x ≤ τ x + ∑ i ∈ Finset.range m, z i := by sorry
