-- Prove2me | Theorems.Thm_GelfandVNA_Duality_proposition_3_8
-- name    : GelfandVNA.Duality.proposition_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:54.280968+00:00
-- url     : https://prove2.me/theorems/1d57e439-8bd9-4b05-9314-e79541dae154
-- title:
--   Proposition 3.8, p. 24 — the projections ProjAlg(A) of a commutative von Neumann algebra form a complete Boolean algebra
-- statement:
--   Let $A$ be a commutative von Neumann algebra. Its projections
--   $$\mathsf{ProjAlg}(A)=\{x\in A\mid x^*=x,\ x^2=x\},$$
--   with multiplication as the Boolean product (meet) and $a\oplus b=(a-b)^2$ as the Boolean sum, form a **complete** Boolean algebra. The statement asserts:
--
--   1. the elements of $\mathsf{ProjAlg}(A)$ are exactly the $x\in A$ with $x^*=x$ and $x^2=x$;
--   2. the meet of $p$ and $q$ is $pq$;
--   3. the symmetric difference of $p$ and $q$ is $(p-q)^2$;
--   4. every subset of $\mathsf{ProjAlg}(A)$ has a least upper bound.
--
--   Completeness is what makes $\mathsf{ProjAlg}(A)$ a candidate measurable locale; it uses that $A$ has a predual.
--
--   **Formalization Note** The Boolean structure on `ProjAlg A` is the one of the VNA module (a Boolean subalgebra of the idempotents); clauses 2–3 identify its operations with the ring operations of the page.
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, p. 24, Proposition 3.8

import Mathlib
import Definitions.Def_GelfandVNA_Duality_VNA

namespace GelfandVNA.Duality

universe u

/-- Proposition 3.8, p. 24: for a commutative von Neumann algebra `A`, the projections
`ProjAlg(A) = {x ∈ A | x* = x, x² = x}`, with multiplication as meet and `a ⊕ b = (a - b)²` as
addition, form a complete Boolean algebra. -/
theorem proposition_3_8 (A : Type u) [CommCStarAlgebra A] [WStarAlgebra A] :
    (∀ x : A, (∃ p : ProjAlg A, p.val = x) ↔ (star x = x ∧ x * x = x)) ∧
    (∀ p q : ProjAlg A, (p ⊓ q).val = p.val * q.val) ∧
    (∀ p q : ProjAlg A, (symmDiff p q).val = (p.val - q.val) ^ 2) ∧
    (∀ s : Set (ProjAlg A), ∃ a : ProjAlg A, IsLUB s a) := by sorry

end GelfandVNA.Duality
