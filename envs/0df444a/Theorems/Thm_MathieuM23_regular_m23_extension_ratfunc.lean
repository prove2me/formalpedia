-- Prove2me | Theorems.Thm_MathieuM23_regular_m23_extension_ratfunc
-- name    : MathieuM23.regular_m23_extension_ratfunc
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-04T17:17:57.960156+00:00
-- url     : https://prove2.me/theorems/8cbef803-4ad4-4f0e-a6c1-b5aba6fa0f22
-- title:
--   Theorem 1.3 — a regular $M_{23}$-extension of $\mathbb{Q}(t)$
-- statement:
--   There exists a finite Galois extension $L/\mathbb{Q}(t)$ that is regular over $\mathbb{Q}$ (contains no nontrivial algebraic extension of $\mathbb{Q}$) and has Galois group isomorphic to $M_{23}$:
--
--   $$\exists\,L/\mathbb{Q}(t)\ \text{finite, Galois, regular}:\qquad \mathrm{Gal}(L/\mathbb{Q}(t))\cong M_{23}.$$
--
--   By Hilbert's irreducibility theorem this implies Theorem 1.1, and in fact gives infinitely many $M_{23}$-extensions of $\mathbb{Q}$.
--
--   **Formalization Note** $\mathbb{Q}(t)$ is the field of rational functions over $\mathbb{Q}$. Regularity is the predicate from the definition file.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 2, Theorem 1.3 (with the definition of regular in §1.2)

import Definitions.Def_MathieuM23_Group
import Definitions.Def_MathieuM23_Regular

namespace MathieuM23

theorem regular_m23_extension_ratfunc :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (RatFunc ℚ) L),
      FiniteDimensional (RatFunc ℚ) L ∧ IsGalois (RatFunc ℚ) L ∧ IsRegularOverRatFunc L ∧
        Nonempty ((L ≃ₐ[RatFunc ℚ] L) ≃* M23) := by sorry

end MathieuM23
