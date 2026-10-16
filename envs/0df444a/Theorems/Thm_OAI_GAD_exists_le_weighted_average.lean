-- Prove2me | Theorems.Thm_OAI_GAD_exists_le_weighted_average
-- name    : OAI.GAD.exists_le_weighted_average
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:57:52.420809+00:00
-- url     : https://prove2.me/theorems/ef5017c9-26c4-44ed-81a7-60c61537bb11
-- title:
--   Some value of a function is at most its weighted average
-- statement:
--   Let $\alpha$ be a finite set, let $q:\alpha\to\mathbb{R}$ be a probability vector, i.e. $q(a)\ge0$ for all $a\in\alpha$ and $\sum_{a\in\alpha}q(a)=1$, and let $f:\alpha\to\mathbb{R}$ be an arbitrary function.
--
--   **Theorem.** There exists $a\in\alpha$ such that
--
--   $$
--   f(a)\le\sum_{b\in\alpha}q(b)\,f(b).
--   $$
--
--   In probabilistic language: some outcome of a random variable on a finite probability space is at most its expectation. This is the probabilistic-method step of random coding: if a codebook drawn at random has small expected cost, then some fixed codebook has cost at most this expectation.
--
--   **Formalization Note** The set $\alpha$ is a `Fintype`; it is automatically nonempty because the weights sum to $1$. No sign condition on $f$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/FinitePacking.lean#L53-L67

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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalProjectors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialDecoder

open OAI OAI.GAD
universe u_1 u_2 u_3
open scoped BigOperators
variable {α : Type u_1} [Fintype α]

theorem OAI.GAD.exists_le_weighted_average (q : α → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hs : ∑ a, q a=1) (f : α → ℝ) : ∃ a, f a ≤ ∑ b, q b*f b := by sorry
