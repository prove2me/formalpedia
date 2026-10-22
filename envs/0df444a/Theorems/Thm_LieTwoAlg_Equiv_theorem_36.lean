-- Prove2me | Theorems.Thm_LieTwoAlg_Equiv_theorem_36
-- name    : LieTwoAlg.Equiv.theorem_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:44.078715+00:00
-- url     : https://prove2.me/theorems/4d328ca9-e105-4f4c-8186-1b0d78d6889e
-- title:
--   Theorem 36, p. 30 — Lie2Alg and 2TermL∞ are equivalent
-- statement:
--   Over a field $k$ of characteristic different from $2$, the category $\mathrm{Lie2Alg}$ of semistrict Lie $2$-algebras and their homomorphisms is equivalent to the category $\mathrm{2Term}L_\infty$ of two-term $L_\infty$-algebras and their homomorphisms:
--
--   $$
--   \mathrm{Lie2Alg}\simeq\mathrm{2Term}L_\infty.
--   $$
--
--   An equivalence here consists of functors in both directions and natural isomorphisms from their composites to the respective identity functors, with invertible lawful components. The categories use the complete coherence and homomorphism equations in Definitions 22–23, Lemma 33, and Definition 34.
--
--   **Formalization Note** Category laws are separate obligations in Propositions 25 and 35. The raw-category equivalence predicate records the one-categorical content of the paper's Theorem 36.
-- source:
--   Baez–Crans, Higher-Dimensional Algebra VI: Lie 2-Algebras, arXiv:math/0307263v6, p. 30, Theorem 36

import Mathlib
import Definitions.Def_LieTwoAlg_Equiv_Model

namespace LieTwoAlg.Equiv

universe u

/-- Theorem 36, p. 30: the categories Lie2Alg and 2TermL∞ are equivalent. -/
theorem theorem_36 (k : Type u) [Field k] (h2 : (2 : k) ≠ 0) :
    RawCat.Equivalent (lie2AlgCat k) (twoTermLInfCat k) := by sorry

end LieTwoAlg.Equiv
