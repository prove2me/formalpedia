-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_bounded_trees_modulus_le_zero
-- name    : OAI.RecursivePotentials.bounded_trees_modulus_le_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:10:33.77098+00:00
-- url     : https://prove2.me/theorems/ade1f070-b2fd-4742-a377-c327f514da0e
-- title:
--   Bounded weakly null trees force a nonpositive asymptotic uniform convexity modulus
-- statement:
--   Let $E$ be a real normed space. An *equivalent norm* on $E$ is a seminorm $N$ together with constants $0<a\le b$ such that $a\|x\|\le N(x)\le b\|x\|$ for all $x\in E$. A *cofinite subspace* is a closed linear subspace $F\subseteq E$ such that $E/F$ is finite-dimensional. The (one-sided) *modulus of asymptotic uniform convexity* of $N$ is
--
--   $$\bar\delta_N(t)=\inf_{x\in E,\ N(x)=1}\ \sup_{F}\ \inf_{y\in F,\ N(y)=1}\bigl(N(x+ty)-1\bigr),$$
--
--   the supremum running over all cofinite subspaces $F$ of $E$. A sequence $(d_k)_{k\in\mathbb{N}}$ in $E$ is *weakly null* if $f(d_k)\to0$ as $k\to\infty$ for every continuous linear functional $f:E\to\mathbb{R}$. For a finite sequence $s$ of natural numbers and $k\in\mathbb{N}$, write $|s|$ for the length of $s$ and $s^\frown k$ for $s$ with $k$ appended.
--
--   **Theorem.** Let $E$ be an infinite-dimensional real normed space, $(N,a,b)$ an equivalent norm on $E$, and $u_h(s)\in E$ a family of vectors indexed by $h\in\mathbb{N}$ and finite sequences $s$ of natural numbers. Let $m,M,c>0$ and assume, for every $h\ge1$:
--
--   1. $m\le\|u_h(s)\|\le M$ for every $s$ with $|s|\le h$;
--   2. for every $s$ with $|s|<h$, the sequence of increments $\bigl(u_h(s^\frown k)-u_h(s)\bigr)_{k\in\mathbb{N}}$ is weakly null;
--   3. for every $s$ with $|s|<h$ and every $k$, $\|u_h(s^\frown k)-u_h(s)\|\ge c$.
--
--   Then
--
--   $$\bar\delta_N\Bigl(\frac{ac}{2bM}\Bigr)\le0.$$
--
--   Since the radius $\frac{ac}{2bM}$ is positive, a space carrying such a family of trees of every finite height has no equivalent norm with $\bar\delta_N(t)>0$ for all $t>0$, i.e. no equivalent asymptotically uniformly convex norm. This is the abstract criterion applied to the sequence-tree space, the joined tree space and its zero-root subspace.
--
--   **Formalization Note** `EquivalentNorm E` bundles the seminorm `N` with the constants `lower` $=a$ and `upper` $=b$; `A.modulus t` is defined with Lean's `sInf`/`sSup` on real sets (which return $0$ on empty or unbounded sets), but on an infinite-dimensional space and for $t\ge0$ all the sets involved are nonempty and bounded, so it is the genuine inf-sup-inf above. The family is a function `u : ℕ → List ℕ → E`, and $s^\frown k$ is `s ++ [k]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean#L261-L314

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms

open OAI OAI.RecursivePotentials
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open Filter Topology

theorem OAI.RecursivePotentials.bounded_trees_modulus_le_zero {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : ¬Module.Finite ℝ E) (A : EquivalentNorm E) (u : ℕ → List ℕ → E)
    {m M c : ℝ} (hm : 0 < m) (hM : 0 < M) (hc : 0 < c)
    (hu : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length ≤ h → m ≤ ‖u h s‖ ∧ ‖u h s‖ ≤ M)
    (hd : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      WeaklyNull (fun k => u h (s ++ [k]) - u h s))
    (hdc : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      ∀ k, c ≤ ‖u h (s ++ [k]) - u h s‖) :
    A.modulus (A.lower * c / (2 * A.upper * M)) ≤ 0 := by sorry
