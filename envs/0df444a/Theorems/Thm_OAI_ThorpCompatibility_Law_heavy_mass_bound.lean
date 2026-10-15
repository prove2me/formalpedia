-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_heavy_mass_bound
-- name    : OAI.ThorpCompatibility.Law.heavy_mass_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:45:05.629847+00:00
-- url     : https://prove2.me/theorems/a67837e5-ac41-44b1-9032-61b18245ef1f
-- title:
--   Relative entropy controls the mass of points where $P$ exceeds $H$ times $R$
-- statement:
--   Let $\Omega$ be a finite set and let $P,R$ be probability distributions on $\Omega$ such that $P$ is absolutely continuous with respect to $R$, i.e. $R(x)=0\Rightarrow P(x)=0$. Let $H>0$. Then
--
--   $$
--   (\log H-1)\;P\big(\{x\in\Omega:\ P(x)>H\,R(x)\}\big)\;\le\;D(P\|R),
--   $$
--
--   where $D(P\|R)=\sum_xP(x)\log\frac{P(x)}{R(x)}$ is the relative entropy (Kullback–Leibler divergence).
--
--   For $H>e$ this is a Markov-type bound: the $P$-probability of the set where the likelihood ratio $P/R$ exceeds $H$ is at most $D(P\|R)/(\log H-1)$. It is used to show that a law with small divergence from a reference law, for instance from a uniform law on a set, puts little mass on points that are much heavier than under the reference.
--
--   **Formalization Note** The relative entropy is the finite sum $\sum_xP(x)\log(P(x)/R(x))$ with Lean's conventions $t/0=0$ and $\log 0=0$; under the absolute-continuity hypothesis every term with $R(x)=0$ has $P(x)=0$ and vanishes, so this is the usual divergence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/EntropyBounds.lean#L29-L56

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling

open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α : Type*} [Fintype α]

theorem OAI.ThorpCompatibility.Law.heavy_mass_bound (P R : Law α) {H : ℝ} (hH : 0 < H)
    (hs : ∀ a, R.mass a = 0 → P.mass a = 0) :
    (Real.log H - 1) * P.prob (fun a => H * R.mass a < P.mass a) ≤
      P.relativeEntropy R := by sorry
