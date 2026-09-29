-- Prove2me | Theorems.Thm_Nullstellensatz_jacobson_of_finiteType
-- name    : Nullstellensatz.jacobson_of_finiteType
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T01:40:25.558786+00:00
-- url     : https://prove2.me/theorems/bf07d781-45e9-43f5-8924-15fa1114958d
-- title:
--   Finitely generated algebras over a Jacobson ring
-- statement:
--   Let $R$ be a Jacobson ring and $A$ a finitely generated $R$-algebra. Then $A$ is a Jacobson ring. Furthermore, if $\mathfrak m \subseteq A$ is a maximal ideal, then $\mathfrak m \cap R$ is a maximal ideal of $R$, and
--   $$A/\mathfrak m \text{ is a finite extension of } R/(\mathfrak m \cap R).$$
--
--   A ring is **Jacobson** when every radical ideal is an intersection of maximal ideals. With $R$ a field this contains the first equality of the intersection formula for every finitely generated algebra over a field.
--
--   **Formalization Note.** $\mathfrak m \cap R$ is the preimage of $\mathfrak m$ under $R \to A$ (the map need not be injective). Mathlib's `IsJacobsonRing` asks that every radical ideal equals its Jacobson radical (the intersection of the maximal ideals containing it).
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, section "Generalizations", first displayed theorem (reference [8] of the article).

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem jacobson_of_finiteType {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsJacobsonRing R] [Algebra.FiniteType R A] :
    IsJacobsonRing A ∧
      ∀ m : Ideal A, m.IsMaximal →
        (m.comap (algebraMap R A)).IsMaximal ∧
          Module.Finite (R ⧸ m.comap (algebraMap R A)) (A ⧸ m) := by sorry

end Nullstellensatz
