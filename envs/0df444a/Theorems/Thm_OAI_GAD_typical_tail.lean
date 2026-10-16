-- Prove2me | Theorems.Thm_OAI_GAD_typical_tail
-- name    : OAI.GAD.typical_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:49:13.779626+00:00
-- url     : https://prove2.me/theorems/bc7258cf-a699-478a-9018-7ae88bd35ae3
-- title:
--   Chebyshev bound on the probability of the atypical set
-- statement:
--   Let $\alpha$ be a finite set and $q$ a probability distribution on $\alpha$, i.e. $q(a)\ge0$ for all $a$ and $\sum_{a\in\alpha}q(a)=1$. Write $H(q)=-\sum_aq(a)\log q(a)$ for its Shannon entropy (natural logarithm, $0\log0=0$). For $n\in\mathbb{N}$ and a string $x=(x_1,\dots,x_n)\in\alpha^n$ let $q^n(x)=\prod_{j=1}^nq(x_j)$ be its probability under $n$ independent draws from $q$. For $\delta\in\mathbb{R}$ the string $x$ is called $\delta$-typical if
--
--   $$
--   q^n(x)>0\qquad\text{and}\qquad\Bigl|\sum_{j=1}^n\bigl(-\log q(x_j)-H(q)\bigr)\Bigr|\le n\delta ,
--   $$
--
--   which for $n\ge1$ says $\bigl|-\tfrac1n\log q^n(x)-H(q)\bigr|\le\delta$. Let $T^n_\delta\subseteq\alpha^n$ be the set of $\delta$-typical strings. Finally let
--
--   $$
--   V(q)=\sum_{a\in\alpha}q(a)\bigl(-\log q(a)-H(q)\bigr)^2
--   $$
--
--   be the variance of the information density $-\log q(a)$ under $q$.
--
--   **Theorem.** If $\delta>0$ and $n\ge1$, then
--
--   $$
--   \sum_{x\in\alpha^n\setminus T^n_\delta}q^n(x)\le\frac{V(q)}{n\,\delta^2}.
--   $$
--
--   Thus the probability that $n$ independent samples from $q$ form an atypical string is at most $V(q)/(n\delta^2)$, which tends to $0$ as $n\to\infty$: a quantitative weak law of large numbers for the information density. In coding theorems this controls the probability mass, or the weight of a quantum state, that falls outside a typical set or typical subspace.
--
--   **Formalization Note** The objects are `iidWeight q n x` $=q^n(x)$, `classicalEntropy q` $=H(q)$, `logVariance q` $=V(q)$ and the predicate `IsTypical q δ n x`; the sum is written with `if IsTypical ... then 0 else iidWeight q n x`. Lean's convention $\log0=0$ gives $-\log q(a)$ a value also when $q(a)=0$, but such letters carry weight $0$ in $V(q)$ and cannot occur in a typical string because of the positivity requirement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/TypicalSets.lean#L133-L149

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalSets

open OAI OAI.GAD
universe u_1 u_2
open scoped BigOperators
variable {α : Type u_2} [Fintype α]
attribute [local instance] OAI.GAD.instDecidablePred_oAI

theorem OAI.GAD.typical_tail (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) :
    (∑ x : Fin n → α, if IsTypical q δ n x then 0 else iidWeight q n x) ≤
      logVariance q / ((n:ℝ)*δ^2) := by sorry
