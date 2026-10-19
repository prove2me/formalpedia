-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_averagedModulus_lower_of_witness
-- name    : OAI.RecursivePotentials.averagedModulus_lower_of_witness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:00:05.215744+00:00
-- url     : https://prove2.me/theorems/f70074a1-4145-49f9-b167-6c2b73189caf
-- title:
--   Lower bounds for the averaged asymptotic modulus from cofinite-subspace witnesses
-- statement:
--   For a real normed space $E$, $x,y\in E$ and $t\in\mathbb{R}$ put
--   $$g(x,t,y)=\frac{\|x+ty\|+\|x-ty\|}{2}-1 .$$
--   A *cofinite subspace* of $E$ is a closed linear subspace $F$ such that the quotient $E/F$ is finite-dimensional. The averaged modulus of $E$ at $t$ is
--   $$\bar\delta_E(t)=\inf_{\|x\|=1}\ \sup_{F}\ \inf\bigl\{g(x,t,y):\ y\in F,\ \|y\|\ge1\bigr\},$$
--   where $F$ ranges over the cofinite subspaces of $E$.
--
--   **Theorem.** Let $E$ be a real normed space that is not finite-dimensional, let $t\ge0$ and $c\in\mathbb{R}$. Assume that for every $x\in E$ with $\|x\|=1$ and every $\varepsilon>0$ there is a cofinite subspace $F$ of $E$ such that
--   $$g(x,t,y)\ \ge\ c-\varepsilon\qquad\text{for all }y\in F\text{ with }\|y\|\ge1 .$$
--   Then $c\le\bar\delta_E(t)$.
--
--   The theorem reduces lower bounds for the averaged modulus to a construction: for each unit vector and each tolerance one has to exhibit a single cofinite subspace on which the averaged gain is almost $c$. In tree spaces the natural witnesses are the tails of finite initial subtrees.
--
--   **Formalization Note** The quantities $g$, the inner infimum and $\bar\delta_E$ are `averagedGain x t y`, `averagedInner x t F` and `averagedModulus E t`; they use `sInf` and `sSup` on $\mathbb{R}$, which return $0$ on empty or unbounded sets. Under the hypotheses of the theorem the sets involved are nonempty, the inner sets are bounded below by $\|x\|-1$, and the suprema over $F$ are bounded above by $t$, so these are genuine infima and suprema. A cofinite subspace is a `CofiniteSubspace E` (a submodule with `IsClosed` and `Module.Finite ℝ (E ⧸ space)`), and non-finite-dimensionality is `¬Module.Finite ℝ E`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean#L1219-L1243

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry

open OAI OAI.RecursivePotentials
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem OAI.RecursivePotentials.averagedModulus_lower_of_witness (hE : ¬Module.Finite ℝ E)
    {t c : ℝ} (ht : 0 ≤ t)
    (hw : ∀ x : E, ‖x‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ F : CofiniteSubspace E, ∀ y ∈ F.space, 1 ≤ ‖y‖ → c - ε ≤ averagedGain x t y) :
    c ≤ averagedModulus E t := by sorry
