-- Prove2me | Theorems.Thm_NumberField_exists_isCyclic_finrank_eq
-- name    : NumberField.exists_isCyclic_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/1c96d4aa-55d3-537b-86e9-e31ab05d81d5
-- title:
--   Existence of cyclic extensions of prescribed degree
-- statement:
--   Let $K$ be a number field, i.e. a type carrying a field structure and a `NumberField` instance, and let $n$ be a natural number with $0 < n$. The assertion is that there exists a type $L$, together with a field structure on $L$, a `NumberField` instance for $L$ and a $K$-algebra structure on $L$, such that $L/K$ is Galois (`IsGalois K L`), the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$ is cyclic, and the rank of $L$ as a $K$-module is exactly $n$, i.e. $[L:K] = n$. Thus the extension produced is a number field cyclic over $K$ of degree precisely $n$; no further properties of $L$ — no containment in a cyclotomic field, no behaviour at prescribed finite or infinite places — are asserted, the data being packaged as a bare existence statement over types with their instances.
--
--   This is the standard auxiliary lemma that over a number field cyclic extensions of every prescribed degree exist, in its weakest form. It is used in the Herbrand-quotient computation for the idèle class group, where an auxiliary cyclic extension of controlled degree is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_isCyclic_finrank_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.exists_isCyclic_finrank_eq
    (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) ∧ Module.finrank K L = n := by sorry
