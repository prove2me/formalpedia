-- Prove2me | Theorems.Thm_JeroslowMLP_Value_lemma_4_2
-- name    : JeroslowMLP.Value.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:58:04.79946+00:00
-- url     : https://prove2.me/theorems/79f8345e-be04-4a78-8a34-251d66ff1230
-- title:
--   Lemma 4.2, pp. 156–157 — for bounded S₀, S₁ is the union of the faces G_j cut out by the extreme dual solutions
-- statement:
--   Consider a multi-level program whose feasible set is a polyhedron $S_0=\{x: Ax\ge b\}$, $A\in\mathbb R^{m\times V}$, and suppose $S_0$ is nonempty and bounded. Let $x^1$ be the variables of the last mover (player $0$ here, player 1 in the paper), $A^1$ the corresponding columns of $A$, $c^{11}$ the last mover's cost coefficients on $x^1$, and $\sum_{i\ge2}A^ix^i$ the contribution of all other variables. Let
--   $$D=\{\gamma\in\mathbb R^m:\ \gamma\ge0,\ \gamma A^1=c^{11}\}\qquad (4.11)$$
--   and, for $\gamma\in D$,
--   $$G_\gamma=\Bigl\{x\in S_0:\ c^{11}x^1=\gamma\Bigl(b-\sum_{i\ge2}A^ix^i\Bigr)\Bigr\}. \qquad (4.13)$$
--   Then:
--
--   1. $D$ has finitely many extreme points $\gamma^1,\dots,\gamma^t$;
--   2. $S_1=\bigcup_{j=1}^t G_{\gamma^j}$ (4.12);
--   3. each $G_{\gamma^j}$ is a face of $S_0$;
--   4. for every $x\in S_0$ there is $x'\in S_1$ agreeing with $x$ on all variables of the other players.
--
--   The lemma describes the last mover's reaction set by linear programming duality; it is the basis of the existence argument for three-level programs (Lemma 4.3).
--
--   **Formalization Note** Faces are Mathlib's `IsExtreme` subsets (the empty set counts as a face, as for the paper's faces). The family $\gamma^1,\dots,\gamma^t$ is `Set.extremePoints ℝ D`, not a supplied list.
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), pp. 156–157, Lemma 4.2, (4.11)–(4.13)

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Multilevel

namespace JeroslowMLP.Value

open MultilevelProgram

theorem lemma_4_2 {V : Type} [Fintype V] {m : ℕ} (A : Matrix (Fin m) V ℝ) (b : Fin m → ℝ)
    (G : MultilevelProgram V) (hfeas : G.feasible = polyhedron A b)
    (hne : (polyhedron A b).Nonempty) (hbdd : Bornology.IsBounded (polyhedron A b)) :
    let D : Set (Fin m → ℝ) :=
      {γ | (∀ r, 0 ≤ γ r) ∧ ∀ v, G.owner v = 0 → ∑ r, γ r * A r v = G.cost 0 v}
    let Gface : (Fin m → ℝ) → Set (V → ℝ) := fun γ =>
      {x | x ∈ polyhedron A b ∧
        ∑ v ∈ Finset.univ.filter (fun v => G.owner v = 0), G.cost 0 v * x v =
          ∑ r, γ r * (b r - ∑ v ∈ Finset.univ.filter (fun v => G.owner v ≠ 0), A r v * x v)}
    (Set.extremePoints ℝ D).Finite ∧
    G.solSet 1 = ⋃ γ ∈ Set.extremePoints ℝ D, Gface γ ∧
    (∀ γ ∈ Set.extremePoints ℝ D, IsExtreme ℝ (polyhedron A b) (Gface γ)) ∧
    ∀ x ∈ polyhedron A b, ∃ x' ∈ G.solSet 1, G.AgreeAbove 0 x x' := by sorry

end JeroslowMLP.Value
