-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_jointLaw_first
-- name    : OAI.MatchingEntropy.jointLaw_first
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:07:06.372388+00:00
-- url     : https://prove2.me/theorems/aaf2ede1-858e-4d59-bb4d-75b031d45fc1
-- title:
--   The fibered coupling over a common pushforward has the prescribed first marginal
-- statement:
--   Let $A$ and $B$ be finite sets, $C$ any set, and $f:A\to C$, $g:B\to C$ maps. For weights $p:A\to\mathbb R$ define the pushforward (fiber mass) $f_*p(c)=\sum_{a\in A:\,f(a)=c}p(a)$, and similarly $g_*q$ for $q:B\to\mathbb R$. The *fibered coupling* of $p$ and $q$ is
--
--   $$
--   J(a,b)=\begin{cases}\dfrac{p(a)\,q(b)}{f_*p\big(f(a)\big)}, & f(a)=g(b),\\ 0, & f(a)\neq g(b),\end{cases}
--   $$
--
--   where a fraction with zero denominator is read as $0$. Assume that $p(a)\ge0$ for all $a$ and that the two pushforwards agree, $f_*p(c)=g_*q(c)$ for every $c\in C$. Then for every $a\in A$,
--
--   $$
--   \sum_{b\in B}J(a,b)=p(a).
--   $$
--
--   When $p$ and $q$ are probability laws, $J$ is the coupling that makes the two coordinates conditionally independent given the common label $f(a)=g(b)$, and the theorem says that its first marginal is $p$ (the second marginal is $q$ by the symmetric argument). It is used to glue laws of perfect matchings on the two sides of a tight cut, the label being the edge used across the cut.
--
--   **Formalization Note** The pushforward is `fiberMass p f c` and the coupling is `jointLaw p q f g (a, b)`. The weights $q$ need not be nonnegative for this identity. Lean's convention $x/0=0$ is the reading of the fraction above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Coupling.lean#L48-L66

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter

theorem OAI.MatchingEntropy.jointLaw_first {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (a : A) : (∑ b, jointLaw p q f g (a,b)) = p a := by sorry
