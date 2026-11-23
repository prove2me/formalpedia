-- Prove2me | Theorems.Thm_Leopoldt_S3Certificate_leopoldtConjecture_cubicK_five
-- name    : Leopoldt.S3Certificate.leopoldtConjecture_cubicK_five
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-23T03:17:30.964108+00:00
-- url     : https://prove2.me/theorems/1af10dfd-31b3-4010-baa5-bfa20f140888
-- title:
--   Leopoldt at five for the splitting field of $X^3-25X-1$
-- statement:
--   Let $K$ be the splitting field of $X^3-25X-1$ over $\mathbb{Q}$. Leopoldt's conjecture holds for $K$ at $p=5$. Equivalently, the closure of the diagonal image of $\mathcal{O}_K^\times$ in the product of the local unit groups at primes above $5$ has $\mathbb{Z}_5$-rank $5$, the rank of the global units.
--
--   $$\delta_5(K)=0.$$
--
--   This is the instance $t=p=5$ of Ferri and Johnston's family of totally real $S_3$-extensions.
-- source:
--   Fabio Ferri and Henri Johnston, Applications of representation theory and of explicit units to Leopoldt’s conjecture, §6, Theorem 6.5, at t=p=5. https://doi.org/10.1007/s40993-026-00717-2

import Definitions.Def_LeopoldtDefect
import Mathlib.FieldTheory.SplittingField.Construction

set_option autoImplicit false

theorem Leopoldt.S3Certificate.leopoldtConjecture_cubicK_five :
    let K := (Polynomial.X ^ 3 - Polynomial.C (25 : ℚ) * Polynomial.X - 1).SplittingField
    letI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
    letI : Fact (Nat.Prime 5) := ⟨by decide⟩
    Leopoldt.LeopoldtConjecture 5 K := by sorry
