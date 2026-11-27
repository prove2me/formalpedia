-- Prove2me | Theorems.Thm_NashStackelberg_Supplement_lemma_2
-- name    : NashStackelberg.Supplement.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:35:06.140787+00:00
-- url     : https://prove2.me/theorems/20c2ea46-c941-4920-8613-0e30141c4937
-- title:
--   Lemma 2 — extended formulations as Stackelberg feasible regions are closed under Cartesian products
-- statement:
--   A set $S\subseteq\mathbb R^m$ has an **extended formulation as a Stackelberg feasible region** if it is the projection onto $s$ of a set $\{(s,u,y): A_L(s,u)+B_Ly\le b_L,\ y\in\mathrm{SOL}(s,u)\}$, where $\mathrm{SOL}(s,u)$ is the optimal set of a single follower's linear program $\min_y (c+H(s,u))^\top y$ s.t. $A(s,u)+By\le b$.
--
--   **Lemma 2.** Let $S\subseteq\mathbb R^{n_1}$ and $T\subseteq\mathbb R^{n_2}$ be arbitrary sets that have extended formulations as Stackelberg feasible regions. Then
--   $$
--   S\times T\subseteq\mathbb R^{n_1+n_2}
--   $$
--   has an extended formulation as a Stackelberg feasible region.
--
--   Together with Lemma 1, this lets the hardness proof of Theorem 2 collect several gadgets into the feasible region of one leader with one linear follower, as a trivial NASP requires.
--
--   **Formalization Note** The notion is `HasStackelbergExtForm`; $S\times T$ is the set of vectors whose first $n_1$ coordinates lie in $S$ and whose last $n_2$ coordinates lie in $T$.
--
--   Differences from the source:
--   - reading: "Stackelberg feasible region" (not defined in the paper) → HasStackelbergExtForm: projection of the feasible region of a simple Stackelberg game with a single LP follower whose objective may carry the simple parameterization (H w)ᵀ y, in hypothesis and conclusion alike; reason: the proof's form {(w, y) : A w + B y ≤ b, y ∈ argmin{fᵀy : C w + D y ≤ g}} with the follower of a trivial NASP (Definition 8), which is the use of Lemma 2 in Claim 1
--   - encoding: S × T ⊆ ℝ^{n₁} × ℝ^{n₂} → {x : Fin (n₁ + n₂) → ℝ | first n₁ coordinates ∈ S, last n₂ coordinates ∈ T}; reason: Lean convention; same set
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, EC §9.1, Lemma 2, p.30, proof p.31

import Mathlib
import Definitions.Def_NashStackelberg_Supplement_HasStackelbergExtForm

namespace NashStackelberg.Supplement

/-- **Lemma 2: Stackelberg feasible regions are closed under Cartesian products** (Carvalho,
Dragotto, Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6,
EC §9.1, Lemma 2, p.30, proof p.31).

If `S ⊆ ℝ^{n₁}` and `T ⊆ ℝ^{n₂}` have extended formulations as Stackelberg feasible regions,
then so does `S × T ⊆ ℝ^{n₁ + n₂}`.

**Formalization Note.** `S × T` is the set of `x : Fin (n₁ + n₂) → ℝ` whose first `n₁`
coordinates lie in `S` and whose last `n₂` coordinates lie in `T`. -/
theorem lemma_2 {n₁ n₂ : ℕ} (S : Set (Fin n₁ → ℝ)) (T : Set (Fin n₂ → ℝ))
    (hS : HasStackelbergExtForm S) (hT : HasStackelbergExtForm T) :
    HasStackelbergExtForm
      {x : Fin (n₁ + n₂) → ℝ |
        (fun i => x (Fin.castAdd n₂ i)) ∈ S ∧ (fun j => x (Fin.natAdd n₁ j)) ∈ T} := by sorry

end NashStackelberg.Supplement
