-- Prove2me | Theorems.Thm_OAI_Problem346_zero_of_upward_grid
-- name    : OAI.Problem346.zero_of_upward_grid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:00:31.57081+00:00
-- url     : https://prove2.me/theorems/235e77d8-cb7b-4412-8726-9c91e631a41e
-- title:
--   Vanishing propagates down from the top corner of a box under one-step upward cancellation
-- statement:
--   Let $\iota$ be a finite index set, let $M$ be a set with a distinguished element $0$, let $r\in\mathbb{N}$, and let $F:\mathbb{N}^{\iota}\to M$ be an arbitrary function of count vectors $c=(c_i)_{i\in\iota}$. Write $\mathrm{Box}_r=\{c\in\mathbb{N}^{\iota}:\ c_i\le r\text{ for all }i\in\iota\}$, write $\mathbf{r}=(r,\dots,r)$ for its top corner, and write $c+\delta_i$ for the vector obtained from $c$ by increasing its $i$-th coordinate by one. Assume
--
--   1. $F(\mathbf{r})=0$, and
--   2. for every $c\in\mathrm{Box}_r$ and every $i\in\iota$ with $c_i<r$: if $F(c+\delta_i)=0$, then $F(c)=0$.
--
--   Then
--
--   $$
--   F(c)=0\qquad\text{for every }c\in\mathrm{Box}_r .
--   $$
--
--   This is a reverse induction principle on a finite rectangular grid: once vanishing at the top corner can be pulled back along any single upward coordinate step, it reaches every point of the box, and no particular order of the steps has to be chosen. It is used to carry the vanishing of a polynomial attached to the terminal count vector $(r,\dots,r)$ back to the initial count vector $(0,\dots,0)$, one coordinate step at a time.
--
--   **Formalization Note** The value type `M` only carries a `Zero` instance; no algebraic structure is used. The index type is a `Fintype` with decidable equality, count vectors are functions `ι → ℕ`, and $c+\delta_i$ is `Function.update c i (c i + 1)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/GridCancellation.lean#L9-L52

import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondSwap

open OAI OAI.Problem346
open scoped BigOperators

theorem OAI.Problem346.zero_of_upward_grid {ι M : Type*} [Fintype ι] [DecidableEq ι] [Zero M]
    (r : ℕ) (F : (ι → ℕ) → M)
    (hend : F (fun _ => r) = 0)
    (hstep : ∀ (c : ι → ℕ), (∀ i, c i ≤ r) → ∀ i, c i < r →
      F (Function.update c i (c i + 1)) = 0 → F c = 0)
    (c : ι → ℕ) (hc : ∀ i, c i ≤ r) : F c = 0 := by sorry
