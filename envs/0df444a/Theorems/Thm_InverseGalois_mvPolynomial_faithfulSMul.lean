-- Prove2me | Theorems.Thm_InverseGalois_mvPolynomial_faithfulSMul
-- name    : InverseGalois.mvPolynomial_faithfulSMul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T01:35:15.693685+00:00
-- url     : https://prove2.me/theorems/f4ee4ab7-c9a5-44e0-b718-ce81b9f4cc38
-- title:
--   A faithful permutation action stays faithful on polynomials
-- statement:
--   Let a group $G$ act faithfully on an index set $I$, and let $R$ be a nontrivial commutative ring. The induced action on the polynomial ring permutes variables according to $g · X_i = X_{g · i}$ and is faithful:
--
--   $$
--   ∀g,h, (∀p, g · p = h · p) ⇒ g=h.
--   $$
--
--   This lifts faithful permutation representations to faithful actions by ring automorphisms.
-- source:
--   Mathlib, MvPolynomial.rename and its action on variables, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/MvPolynomial/Rename.lean#L54-L83

import Definitions.Def_InverseGalois_regular_action

namespace InverseGalois

theorem mvPolynomial_faithfulSMul (G I R : Type*) [Group G] [CommRing R]
    [Nontrivial R] [MulAction G I] [FaithfulSMul G I] :
    letI := mvPolynomialMulSemiringAction G I R
    FaithfulSMul G (MvPolynomial I R) := by sorry
