-- Prove2me | Theorems.Thm_Leopoldt_exists_algHom_cyclotomicField_of_three_le_finrank
-- name    : Leopoldt.exists_algHom_cyclotomicField_of_three_le_finrank
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T02:22:28.463616+00:00
-- url     : https://prove2.me/theorems/ed1ffaa9-0812-4198-8075-7887c639cf0e
-- title:
--   Kronecker--Weber for abelian fields of degree at least $3$
-- statement:
--   **Kronecker–Weber theorem, degree $\ge 3$.** Let $\mathbb{K}$ be a number field which is a Galois extension of $\mathbb{Q}$ with abelian Galois group $\mathrm{Gal}(\mathbb{K}/\mathbb{Q})$, and assume $[\mathbb{K}:\mathbb{Q}] \ge 3$. Then there is an integer $n \ge 1$ and an embedding of $\mathbb{Q}$-algebras
--   $$\mathbb{K} \hookrightarrow \mathbb{Q}(\zeta_n).$$
--
--   This is the Kronecker–Weber theorem restricted to fields of degree at least $3$. Fields of degree $\le 2$ (the field $\mathbb{Q}$ and the quadratic fields) are handled separately by the elementary Gauss-sum argument, `NumberField.exists_algHom_cyclotomicField_of_finrank_le_two`; the present statement is the part that requires the genuine proof of the theorem (e.g. via ramification groups and reduction to cyclic extensions of prime-power degree, as in Washington's Chapter 14, or via Artin reciprocity).
--
--   **Formalization note.** As in `Leopoldt.exists_algHom_cyclotomicField`, "abelian Galois" is `IsGalois ℚ K` together with `IsMulCommutative (K ≃ₐ[ℚ] K)`, $\mathbb{Q}(\zeta_n)$ is `CyclotomicField n ℚ`, and the embedding is an unspecified `K →ₐ[ℚ] CyclotomicField n ℚ`. The degree hypothesis is `3 ≤ Module.finrank ℚ K`.
-- source:
--   Kronecker-Weber theorem: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Chapter 14, Theorem 14.1 (every finite abelian extension of Q is contained in a cyclotomic field); first complete proof D. Hilbert, 'Ein neuer Beweis des Kronecker'schen Fundamentalsatzes ueber Abel'sche Zahlkoerper', Nachr. Ges. Wiss. Goettingen (1896), 29-39. Here restricted to degree >= 3, the degree <= 2 case being NumberField.exists_algHom_cyclotomicField_of_finrank_le_two.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem exists_algHom_cyclotomicField_of_three_le_finrank (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] [IsMulCommutative (K ≃ₐ[ℚ] K)] (hK : 3 ≤ Module.finrank ℚ K) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by sorry
end Leopoldt
