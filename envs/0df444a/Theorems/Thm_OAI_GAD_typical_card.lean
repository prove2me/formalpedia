-- Prove2me | Theorems.Thm_OAI_GAD_typical_card
-- name    : OAI.GAD.typical_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:54:24.352039+00:00
-- url     : https://prove2.me/theorems/7fa09cb1-bb1d-4484-b484-2f9f4981c5a1
-- title:
--   The typical set has at most $e^{n(H(q)+\delta)}$ elements
-- statement:
--   Let $\alpha$ be a finite set and $q$ a probability distribution on $\alpha$, i.e. $q(a)\ge0$ for all $a$ and $\sum_{a\in\alpha}q(a)=1$. Write $H(q)=-\sum_aq(a)\log q(a)$ for its Shannon entropy (natural logarithm, $0\log0=0$). For $n\in\mathbb{N}$ and a string $x=(x_1,\dots,x_n)\in\alpha^n$ let $q^n(x)=\prod_{j=1}^nq(x_j)$ be its probability under $n$ independent draws from $q$. For $\delta\in\mathbb{R}$ the string $x$ is called $\delta$-typical if
--
--   $$
--   q^n(x)>0\qquad\text{and}\qquad\Bigl|\sum_{j=1}^n\bigl(-\log q(x_j)-H(q)\bigr)\Bigr|\le n\delta ,
--   $$
--
--   which for $n\ge1$ says $\bigl|-\tfrac1n\log q^n(x)-H(q)\bigr|\le\delta$. Let $T^n_\delta\subseteq\alpha^n$ be the set of $\delta$-typical strings.
--
--   **Theorem.** For every $\delta\in\mathbb{R}$ and every $n\in\mathbb{N}$,
--
--   $$
--   |T^n_\delta|\le e^{\,n(H(q)+\delta)} .
--   $$
--
--   This is the standard cardinality bound of the asymptotic equipartition property: every typical string has probability at least $e^{-n(H(q)+\delta)}$, so there cannot be more than $e^{n(H(q)+\delta)}$ of them. In coding theorems it bounds the size of typical sets, and hence the rank of typical projectors, by roughly $e^{nH}$.
--
--   **Formalization Note** The typical set is `typicalSet q δ n`, a `Finset` obtained by filtering all strings with the predicate `IsTypical q δ n` (decided classically), and `classicalEntropy q` $=H(q)$. No restriction on $\delta$ or $n$ is needed; for $n=0$ the only string is the empty one, which is typical, and the bound reads $1\le1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/TypicalSets.lean#L154-L174

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

theorem OAI.GAD.typical_card (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    (δ : ℝ) (n : ℕ) :
    ((typicalSet q δ n).card : ℝ) ≤ Real.exp ((n:ℝ)*(classicalEntropy q+δ)) := by sorry
