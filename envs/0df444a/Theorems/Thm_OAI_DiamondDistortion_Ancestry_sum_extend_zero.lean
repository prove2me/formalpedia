-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_sum_extend_zero
-- name    : OAI.DiamondDistortion.Ancestry.sum_extend_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:49:46.500319+00:00
-- url     : https://prove2.me/theorems/cd6ba11c-7df1-4d46-885f-2ebef1462a74
-- title:
--   Extension by zero along an injection preserves finite sums
-- statement:
--   Let $\kappa$ and $N$ be finite sets, let $e:\kappa\to N$ be injective and let $f:\kappa\to\mathbb{R}$. Let $\tilde f:N\to\mathbb{R}$ be the extension of $f$ by zero along $e$: $\tilde f(e(a))=f(a)$ for $a\in\kappa$, and $\tilde f(i)=0$ for $i\notin e(\kappa)$. Then
--
--   $$
--   \sum_{i\in N}\tilde f(i)=\sum_{a\in\kappa}f(a).
--   $$
--
--   This bookkeeping identity rewrites a sum over a selected subfamily, indexed injectively by $\kappa$, as a sum over all indices of an ambient finite family, with zero contributions at the unselected indices. It is used to pass between the per-selection and the per-segment forms of the split-gain estimates for segment norms.
--
--   **Formalization Note** The extension is `Function.extend e f (fun _ => 0)`, the finite sets are types with `Fintype` instances, and $e$ is an embedding `κ ↪ ν`. The ancestry structure of the surrounding file plays no role in this statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L254-L268

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
universe u v
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
variable {ι : Type*} [A : Ancestry ι]

theorem OAI.DiamondDistortion.Ancestry.sum_extend_zero {κ ν : Type*} [Fintype κ] [Fintype ν]
    (e : κ ↪ ν) (f : κ → ℝ) :
    (∑ i, Function.extend e f (fun _ => 0) i) = ∑ a, f a := by sorry
