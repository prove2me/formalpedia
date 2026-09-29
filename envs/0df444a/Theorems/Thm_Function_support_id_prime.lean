-- Prove2me | Theorems.Thm_Function_support_id_prime
-- name    : Function.support_id_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:41:44.36828+00:00
-- url     : https://prove2.me/theorems/92a059d4-d2f5-4994-b0fa-f2e72da43be1
-- title:
--   The support of the identity function is the complement of $\{0\}$
-- statement:
--   Let $\alpha$ be a type equipped with a zero element. Then the support of the identity function $x \mapsto x$ on $\alpha$ — the set of points where the function is nonzero — is exactly the complement of $\{0\}$:
--   $$\operatorname{supp}(\mathrm{id}) = \{x : x \neq 0\} = \{0\}^{c}.$$
--
--   This is a definitional-level lemma: $x \mapsto x$ vanishes precisely at $x = 0$.
--
--   It serves as a simp-style building block for computing supports of composite functions (products, scalings, compositions with the identity), which in the PNT+ project matter when tracking where mollifiers and smoothed integrands vanish, e.g. to restrict integrals to compact supports in Mellin-transform arguments.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean#L10-L11

import Mathlib.Algebra.Notation.Support

open Function

variable {α : Type*} [Zero α]

theorem Function.support_id_prime {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ := by sorry
