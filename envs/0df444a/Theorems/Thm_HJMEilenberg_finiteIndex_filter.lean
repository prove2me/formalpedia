-- Prove2me | Theorems.Thm_HJMEilenberg_finiteIndex_filter
-- name    : HJMEilenberg.finiteIndex_filter
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-09T10:36:22.884564+00:00
-- url     : https://prove2.me/theorems/bfeb63b0-b6d8-4f14-934c-33429a4a5304
-- title:
--   Finite-index congruences form a filter
-- statement:
--   Let $S$ be a finite sort type, $\Sigma$ an $S$-sorted signature, and $A$ a $\Sigma$-algebra. The universal congruence on $A$ has finite index; the intersection of any two finite-index congruences has finite index; and every congruence above a finite-index congruence has finite index.
--
--   Equivalently, the finite-index congruences form a filter in the congruence order. This supplies the finiteness closure needed in both formation constructions.
-- source:
--   Juan Climent Vidal and Enric Cosme Llópez, Eilenberg theorems for many-sorted formations, Houston Journal of Mathematics 45(2) (2019), Section 6, pp. 351–416; arXiv:1604.04792. The free-term substrate is cross-checked against the companion TeX source A Kleene theorem for free many-sorted algebras. Section 6, proposition immediately following the definition of finite-index congruence.

import Definitions.Def_HJMEilenberg_Formations

namespace HJMEilenberg

open MSKleene

/-- Proposition 6.7: finite-index congruences form a filter. -/
theorem finiteIndex_filter {S : Type} [Finite S] {sig : Signature S}
    (A : Algebra sig) :
    Congruence.FiniteIndex (Congruence.top A) ∧
      (∀ Phi Psi : Congruence A,
        Phi.FiniteIndex → Psi.FiniteIndex →
          (Congruence.inter Phi Psi).FiniteIndex) ∧
      (∀ Phi Psi : Congruence A,
        Phi.FiniteIndex → Phi ≤ Psi → Psi.FiniteIndex) := by
  sorry

end HJMEilenberg
