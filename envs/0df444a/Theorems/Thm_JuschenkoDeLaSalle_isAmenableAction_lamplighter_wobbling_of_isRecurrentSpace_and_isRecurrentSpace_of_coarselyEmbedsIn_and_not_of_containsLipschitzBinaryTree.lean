-- Prove2me | Theorems.Thm_JuschenkoDeLaSalle_isAmenableAction_lamplighter_wobbling_of_isRecurrentSpace_and_isRecurrentSpace_of_coarselyEmbedsIn_and_not_of_containsLipschitzBinaryTree
-- name    : JuschenkoDeLaSalle.isAmenableAction_lamplighter_wobbling_of_isRecurrentSpace_and_isRecurrentSpace_of_coarselyEmbedsIn_and_not_of_containsLipschitzBinaryTree
-- status  : Disproved
-- author  : @dbenbenn
-- created : 2026-10-07T09:29:57.387245+00:00
-- url     : https://prove2.me/theorems/fdc71ea4-94f5-4a2b-a293-eea05abe01f2
-- title:
--   Juschenko–de la Salle, Theorem 1.4 — the lamplighter action of W(X) is amenable for recurrent X, and not if X contains a Lipschitz binary tree
-- statement:
--   Let $X$ be a metric space with bounded geometry: for every $R > 0$, the closed balls of radius $R$ are finite with a common bound on their sizes. Let $W(X)$ be its wobbling group, the permutations $g$ of $X$ with $\sup_x d(gx, x) < \infty$, and consider the action of the lamplighter group $(\mathbf Z/2\mathbf Z)^{(X)} \rtimes W(X)$ on the finitely supported configurations $(\mathbf Z/2\mathbf Z)^{(X)}$ by $(f, g)\cdot f' = f + g f'$. Then:
--
--   1. if $X$ is recurrent at some point $x_0$ — for every $R > 0$, the random walk started at $x_0$ that jumps from $x$ to a uniformly chosen point of the closed ball $B(x, R)$ returns to $x_0$ with probability $1$ — the action is amenable;
--   2. if $X$ embeds coarsely in $\mathbf Z^2$ — there are $f : X \to \mathbf Z^2$ and functions $\rho_- \le \rho_+$ with $\rho_-(t) \to \infty$ and $\rho_-(d(x,y)) \le d(f x, f y) \le \rho_+(d(x,y))$ — then $X$ is recurrent at every point; this covers $X = \mathbf Z$ and $X = \mathbf Z^2$;
--   3. if $X$ contains an injective Lipschitz image of the infinite rooted binary tree with its path metric, the action is not amenable.
--
--   Juschenko and de la Salle, p. 2: “Theorem 1.4. Let $(X, d)$ be a metric space with bounded geometry. • If $(X, d)$ is recurrent, then the action of $\bigoplus_X \mathbb Z/2\mathbb Z \rtimes W(X)$ on $\bigoplus_X \mathbb Z/2\mathbb Z$ is amenable. This includes $X = \mathbb Z, \mathbb Z^2$ or more generally a metric space $(X, d)$ with bounded geometry that embeds coarsely in $\mathbb Z^2$. • If $X$ contains a Lipschitz and injective image of the infinite binary tree, then the action of $\bigoplus_X \mathbb Z/2\mathbb Z \rtimes W(X)$ on $\bigoplus_X \mathbb Z/2\mathbb Z$ is not amenable.” Recurrence is Definition 1.3 (p. 2).
--
--   *Formalization note.* The sentence “This includes …” is clause 2: such spaces are recurrent, so clause 1 applies to them. Recurrence is assumed at one point $x_0$; the paper notes that it does not depend on $x_0$ (p. 2). The paper does not say whether $B(x, R)$ is open or closed; the closed ball is taken.
-- source:
--   Juschenko, K. and de la Salle, M., Invariant means for the wobbling group, Bull. Belg. Math. Soc. Simon Stevin 22 (2015) 281–290, https://doi.org/10.36045/bbms/1432840864 (arXiv:1301.4736v4, whose page numbers are used), p. 2, Theorem 1.4

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace JuschenkoDeLaSalle

theorem isAmenableAction_lamplighter_wobbling_of_isRecurrentSpace_and_isRecurrentSpace_of_coarselyEmbedsIn_and_not_of_containsLipschitzBinaryTree
    {X : Type*} [MetricSpace X] (hX : HasBoundedGeometry X) :
    (∀ x₀ : X, IsRecurrentSpace X x₀ →
      IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2))) ∧
    (CoarselyEmbedsIn X (Fin 2 → ℤ) → ∀ x₀ : X, IsRecurrentSpace X x₀) ∧
    (ContainsLipschitzBinaryTree X →
      ¬ IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2))) := by
  sorry

end JuschenkoDeLaSalle
