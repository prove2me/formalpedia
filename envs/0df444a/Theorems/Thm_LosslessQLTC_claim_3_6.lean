-- Prove2me | Theorems.Thm_LosslessQLTC_claim_3_6
-- name    : LosslessQLTC.claim_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:22:14.837147+00:00
-- url     : https://prove2.me/theorems/9625042c-4fc8-4312-8649-ae2e46b73f32
-- title:
--   Claim 3.6, p.23 — intervals below non-colliding vertices are Boolean cubes
-- statement:
--   Let $v\in V_\emptyset$. For every $x_I\in G$, the interval $[v,x_I]=\{y:v\le y\le x_I\}$ satisfies:
--
--   1. For every $J\subseteq I$, there is a unique vertex $x_J\in[v,x_I]\cap\mathrm{Lk}_J(v)$.
--   2. For every $J,K\subseteq I$, we have $x_J\le x_K$ if and only if $J\subseteq K$. In particular, the interval is an $|I|$-dimensional Boolean cube.
--   3. Every four-cycle in this interval is a square in $X(2)$.
--
--   So the part of the link away from collisions looks locally like the complete multipartite complex.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: the reference ordering of each type $I$ is fixed arbitrarily → the increasing ordering of $I$; reason: Lemma 3.3 makes the fiber size independent of the ordering
--   - reading: a four-cycle in the interval → vertices $c\lessdot b,b'\lessdot a$ in the interval with $b\ne b'$; reason: the proof on p.24 treats exactly these two-dimensional faces of the cube
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Claim 3.6, p.23

import Mathlib
import Definitions.Def_LosslessQLTC_Paths

namespace LosslessQLTC

/-- Claim 3.6 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.23): for `v ∈ V_∅` and
`x_I ∈ G`, the interval `[v, x_I] = {y : v ≤ y ≤ x_I}` satisfies:
(1) for every `J ⊆ I` there is a unique vertex `x_J ∈ [v, x_I] ∩ Lk_J(v)`;
(2) for every `J, K ⊆ I`, `x_J ≤ x_K` if and only if `J ⊆ K`, so that the interval is an
    `|I|`-dimensional Boolean cube;
(3) every four-cycle in this interval is a square in `X(2)`.

**Formalization Note.** In (2) the vertices `x_J`, `x_K` are named by their defining property. In
(3) a four-cycle `c ⋖ b, b′ ⋖ a` with `b ≠ b′` is a two-dimensional face of the cube (p.24). -/
theorem claim_3_6 {k : ℕ} (X : SquareComplex k) (v : X.Vtx) (hv : X.type v = ∅) (x : X.Vtx)
    (hx : x ∈ goodSet X v) :
    (∀ J : Finset (Fin k), J ⊆ X.type x →
      ∃! y, Relation.ReflTransGen X.up v y ∧ Relation.ReflTransGen X.up y x ∧
        y ∈ LkType X v J) ∧
    (∀ (J K : Finset (Fin k)) (yJ yK : X.Vtx), J ⊆ X.type x → K ⊆ X.type x →
      Relation.ReflTransGen X.up yJ x → yJ ∈ LkType X v J →
      Relation.ReflTransGen X.up yK x → yK ∈ LkType X v K →
      (Relation.ReflTransGen X.up yJ yK ↔ J ⊆ K)) ∧
    (∀ a b b' c : X.Vtx,
      Relation.ReflTransGen X.up v c → Relation.ReflTransGen X.up a x →
      X.up c b → X.up c b' → X.up b a → X.up b' a → b ≠ b' →
      X.Square a b b' c) := by sorry

end LosslessQLTC
