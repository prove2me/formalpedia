-- Prove2me | Theorems.Thm_OAI_GAD_sequential_union_bound
-- name    : OAI.GAD.sequential_union_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:02:30.680985+00:00
-- url     : https://prove2.me/theorems/f836c8e5-d825-43e4-a95c-e846e28c0de7
-- title:
--   Union bound for sequential orthogonal projections in a real inner product space
-- statement:
--   Let $E$ be a real inner product space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$. Let $P_0,P_1,P_2,\dots:E\to E$ be maps (not assumed linear) such that, for every $i$, each value of $P_i$ is orthogonal to each residual of $P_i$:
--   $$\langle P_ix,\;y-P_iy\rangle=0\qquad\text{for all }x,y\in E .$$
--   Let $(u_i)_{i\ge0}$ be a sequence obtained by applying the maps in turn, $u_{i+1}=P_i(u_i)$ for all $i$. Then for every $n\in\mathbb{N}$,
--
--   $$
--   \|u_0\|^2-\|u_n\|^2\;\le\;4\sum_{i=0}^{n-1}\bigl\|u_0-P_i(u_0)\bigr\|^2 .
--   $$
--
--   Orthogonal projections onto closed subspaces satisfy the hypothesis. The inequality is a deterministic form of the quantum union bound: if each projection $P_i$ on its own nearly preserves the initial vector $u_0$, then applying the projections one after another loses little squared norm, and the total loss is at most four times the sum of the individual losses $\|u_0-P_iu_0\|^2$. For $n=0$ both sides vanish.
--
--   **Formalization Note** The hypothesis is `∀ i x y, ⟪P i x, y - P i y⟫_ℝ = 0`; $E$ is any type with `NormedAddCommGroup` and `InnerProductSpace ℝ E` instances, so complex Hilbert spaces are covered through their real inner product $\operatorname{Re}\langle\cdot,\cdot\rangle$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/SequentialProjections.lean#L11-L54

import Mathlib
import Definitions.Def_AmplitudeDamping

open OAI OAI.GAD
universe u_1
open scoped BigOperators InnerProductSpace

theorem OAI.GAD.sequential_union_bound {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ℕ → E → E) (hP : ∀ i x y, ⟪P i x, y-P i y⟫_ℝ = 0)
    (u : ℕ → E) (hu : ∀ i, u (i+1)=P i (u i)) (n : ℕ) :
    ‖u 0‖^2-‖u n‖^2 ≤ 4 * ∑ i ∈ Finset.range n, ‖u 0-P i (u 0)‖^2 := by sorry
