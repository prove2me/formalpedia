-- Prove2me | Theorems.Thm_NashStackelberg_Supplement_lemma_1
-- name    : NashStackelberg.Supplement.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:34:18.979787+00:00
-- url     : https://prove2.me/theorems/91f32087-4c6c-4ae7-9dfb-e450e1602292
-- title:
--   Lemma 1 — $\{h=w,\,y=1\}\cup\{h=0,\,y=0\}$ in $\mathbb R^3_+$ is a projected Stackelberg feasible region
-- statement:
--   Consider the union of two polyhedra in $\mathbb R^3_+$,
--   $$
--   \mathcal S=\{(h,y,w)\in\mathbb R^3_+:\ h=w,\ y=1\}\ \cup\ \{(h,y,w)\in\mathbb R^3_+:\ h=0,\ y=0\}.
--   $$
--
--   **Lemma 1.** $\mathcal S$ has an extended formulation as the feasible set of a simple Stackelberg game: there are a single follower solving a linear program with a simple parameterization in the leader's variables, and linear leader constraints, such that $\mathcal S$ is the projection onto $(h,y,w)$ of the set of points (leader variables, follower response) satisfying the leader constraints with the follower's response optimal.
--
--   The set $\mathcal S$ encodes the product $h=wy$ for $y\in\{0,1\}$; it is the gadget that lets a linear follower model a bilinear term in the hardness proof of Theorem 2.
--
--   **Formalization Note** Points of $\mathbb R^3$ are maps $x:\{0,1,2\}\to\mathbb R$ with $(h,y,w)=(x_0,x_1,x_2)$. The notion of extended formulation is `HasStackelbergExtForm`.
--
--   Differences from the source:
--   - generalization: "feasible set of a simple Stackelberg game" (Definition 3: any facile followers' game) → feasible region of a simple Stackelberg game with a single follower solving an LP with a simple parameterization (FollowerGame with K = 1, Q = 0); reason: the proof (7a)–(7b) has exactly this form and Lemma 1 builds the trivial NASP of Theorem 2 (Claim 1); this class is contained in the simple Stackelberg games, so the Lean statement (a formulation in a smaller class exists) implies the source's claim
--   - reading: "has an extended formulation as" → S is the projection onto (h, y, w) of the Stackelberg feasible region, extra leader variables u and the follower's variables being existentially quantified; reason: the proof: "variables in the lifted space, i.e., variables that can be projected out"
--   - encoding: (h, y, w) ∈ ℝ³₊ → x : Fin 3 → ℝ with h = x 0, y = x 1, w = x 2, all three nonnegative; reason: Lean convention; same set
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, EC §9.1, Lemma 1, p.30, proof (7a)–(7b), p.30

import Mathlib
import Definitions.Def_NashStackelberg_Supplement_HasStackelbergExtForm

namespace NashStackelberg.Supplement

/-- **Lemma 1: a union of two polyhedra in ℝ³₊ as a Stackelberg feasible region** (Carvalho,
Dragotto, Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6,
EC §9.1, Lemma 1, p.30).

The set
`𝒮 = {(h, y, w) ∈ ℝ³₊ : h = w, y = 1} ∪ {(h, y, w) ∈ ℝ³₊ : h = 0, y = 0}`
has an extended formulation as the feasible set of a simple Stackelberg game: it is the
projection onto `(h, y, w)` of the feasible region of a simple Stackelberg game whose leader
controls `(h, y, w)` (and possibly extra variables) and whose single follower solves a linear
program with a simple parameterization in the leader's variables.

**Formalization Note.** A point of `ℝ³` is `x : Fin 3 → ℝ` with `h = x 0`, `y = x 1`,
`w = x 2`; `ℝ³₊` requires all three coordinates nonnegative. -/
theorem lemma_1 :
    HasStackelbergExtForm
      {x : Fin 3 → ℝ | (0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2) ∧
        ((x 0 = x 2 ∧ x 1 = 1) ∨ (x 0 = 0 ∧ x 1 = 0))} := by sorry

end NashStackelberg.Supplement
