-- Prove2me | Theorems.Thm_LosslessQLTC_lemma_3_3
-- name    : LosslessQLTC.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:22:41.133859+00:00
-- url     : https://prove2.me/theorems/4c296a24-5a0f-4ae1-84f0-5bd724317c2d
-- title:
--   Lemma 3.3, p.21 — the fiber size does not depend on the ordering
-- statement:
--   Let $v\in V_\emptyset$ and $I\subseteq[k]$. For every $x\in\mathrm{Lk}_I(v)$, the fiber size $|\mathrm{End}_\pi^{-1}(x)|$ is independent of the ordering $\pi$ of $I$. Here the fiber is the set of monotone paths from $v$ to $x$ whose directions appear in the order $\pi$. This makes the notion of a colliding endpoint independent of any reference ordering.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: an ordering $\pi:[i]\twoheadrightarrow I$ and paths $(x_0,\dots,x_i)$ → a duplicate-free list with underlying set $I$, and functions on `Fin (π.length + 1)`; reason: same objects
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Lemma 3.3, p.21

import Mathlib
import Definitions.Def_LosslessQLTC_Paths

namespace LosslessQLTC

/-- Lemma 3.3 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.21): for `v ∈ V_∅`, `I ⊆ [k]`
and `x ∈ Lk_I(v)`, the fiber size `|End_π⁻¹(x)|` is independent of the ordering `π` of `I`. -/
theorem lemma_3_3 {k : ℕ} (X : SquareComplex k) (v : X.Vtx) (hv : X.type v = ∅)
    (I : Finset (Fin k)) (x : X.Vtx) (hx : x ∈ LkType X v I) (π π' : List (Fin k))
    (hπ : IsOrdering π I) (hπ' : IsOrdering π' I) :
    (fiber X v π x).card = (fiber X v π' x).card := by sorry

end LosslessQLTC
