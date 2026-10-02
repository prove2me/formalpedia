-- Prove2me | Theorems.Thm_LeblSCV_Pseudoconvex_hartogs_pseudoconvex_local
-- name    : LeblSCV.Pseudoconvex.hartogs_pseudoconvex_local
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T05:57:31.825773+00:00
-- url     : https://prove2.me/theorems/bfcca5ca-38bc-4a4c-b90a-dbaac413b6b6
-- title:
--   Lemma 2.5.7 — Hartogs pseudoconvexity is a local property of the boundary
-- statement:
--   A domain $U \subset \mathbb{C}^n$ is Hartogs pseudoconvex if and only if every point $p \in \partial U$ has a neighborhood $W$ such that $W \cap U$ is Hartogs pseudoconvex:
--   $$U \text{ Hartogs pseudoconvex} \iff \forall p \in \partial U \ \exists W \ni p \text{ open with } W \cap U \text{ Hartogs pseudoconvex}.$$
--
--   Locality is what allows local boundary conditions to decide pseudoconvexity, as in the proof that Levi and Hartogs pseudoconvexity agree for smooth boundaries (Theorem 2.5.8).
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. The neighborhood $W$ is an open set containing $p$. As in the book, “$W \cap U$ is Hartogs pseudoconvex” includes that $W \cap U$ is a domain, since Hartogs pseudoconvexity is defined for domains.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 94, Lemma 2.5.7

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsHartogsPseudoconvex

namespace LeblSCV.Pseudoconvex

/-- Lemma 2.5.7 (Lebl, p. 94). A domain `U ⊂ ℂⁿ` is Hartogs pseudoconvex iff for every point
`p ∈ ∂U` there exists a neighborhood `W` of `p` (open, containing `p`) such that `W ∩ U` is
Hartogs pseudoconvex (in particular a domain). -/
theorem hartogs_pseudoconvex_local {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUo : IsOpen U) (hUc : IsConnected U) :
    IsHartogsPseudoconvex U ↔
      ∀ p ∈ frontier U, ∃ W : Set (EuclideanSpace ℂ (Fin n)),
        IsOpen W ∧ p ∈ W ∧ IsHartogsPseudoconvex (W ∩ U) := by sorry

end LeblSCV.Pseudoconvex
