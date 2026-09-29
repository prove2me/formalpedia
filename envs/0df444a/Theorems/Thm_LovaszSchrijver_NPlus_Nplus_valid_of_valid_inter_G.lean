-- Prove2me | Theorems.Thm_LovaszSchrijver_NPlus_Nplus_valid_of_valid_inter_G
-- name    : LovaszSchrijver.NPlus.Nplus_valid_of_valid_inter_G
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:59:23.006794+00:00
-- url     : https://prove2.me/theorems/b83092ab-c29b-4f84-b5aa-161391e80a2c
-- title:
--   Lemma 1.5 — sign-restricted inequalities valid on every K ∩ Gᵢ are valid for N₊(K)
-- statement:
--   Let $K \subseteq Q$ be a closed convex cone in $\mathbb R^{n+1}$, where $Q$ is the cone spanned by the 0–1 vectors with $x_0 = 1$, and let $G_i = \{x : x_i = x_0\}$. Let $a \in \mathbb R^{n+1}$ satisfy $a_i \le 0$ for $i = 1, \dots, n$ and $a_0 \ge 0$. Assume that for every $i$ with $a_i < 0$,
--   $$a^{\mathsf T}x \ge 0 \quad \text{for all } x \in K \cap G_i .$$
--   Then
--   $$a^{\mathsf T}x \ge 0 \quad \text{for all } x \in N_+(K).$$
--
--   This is the positive-semidefinite analogue of the paper's Lemma 1.3: it certifies inequalities for one round of $N_+$ from their validity on the faces $K \cap G_i$, and it is the engine behind Lemma 2.14.
--
--   **Formalization Note** The hypothesis that $K$ is closed is added. Condition (iii) of the definition of $M(K, Q)$ sees $K$ only through its polar cone, so $N_+(K)$ depends only on the closure of $K$; the paper's reformulation (iii″) on p. 170, which the proof uses, needs $K$ closed. The paper's cones are polyhedral in every application. Coordinates: $a_0$ is `a none`, $a_i$ is `a (some i)`.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 172, Lemma 1.5

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_MatrixCone

namespace LovaszSchrijver.NPlus

theorem Nplus_valid_of_valid_inter_G {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKQ : K ⊆ Q) (hKc : IsClosed K)
    (a : Option ι → ℝ) (ha : ∀ i : ι, a (some i) ≤ 0) (ha₀ : 0 ≤ a none)
    (hvalid : ∀ i : ι, a (some i) < 0 → ∀ x ∈ K ∩ G i, 0 ≤ a ⬝ᵥ x) :
    ∀ x ∈ N1plus K, 0 ≤ a ⬝ᵥ x := by sorry

end LovaszSchrijver.NPlus
