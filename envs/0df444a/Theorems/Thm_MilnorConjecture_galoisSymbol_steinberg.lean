-- Prove2me | Theorems.Thm_MilnorConjecture_galoisSymbol_steinberg
-- name    : MilnorConjecture.galoisSymbol_steinberg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T12:05:31.212326+00:00
-- url     : https://prove2.me/theorems/c72d027a-e0d4-4746-a33a-4e4d84c340ec
-- title:
--   Steinberg relation for the Galois symbol
-- statement:
--   Let $F$ be a field of characteristic different from $2$, let $F^{\mathrm{sep}}$ be a separable closure and $G_F=\operatorname{Gal}(F^{\mathrm{sep}}/F)$. For $a\in F^\times$ let $\chi_a:G_F\to\mathbb{Z}/2$ be the Kummer character ($\chi_a(\sigma)=0$ iff $\sigma$ fixes a chosen square root of $a$). For $a=(a_1,\dots,a_n)\in(F^\times)^n$, the Galois symbol $\mathrm{gs}(a_1,\dots,a_n)\in H^n(F,\mathbb{Z}/2)$ is the cup product $\chi_{a_1}\cup\cdots\cup\chi_{a_n}$ in continuous Galois cohomology (with $\mathrm{gs}()=1\in H^0$).
--
--   Then the Galois symbol satisfies the Steinberg relation: if two adjacent entries satisfy $a_i+a_{i+1}=1$, then
--
--   $$\mathrm{gs}(a_1,\dots,a_n)=0\in H^n(F,\mathbb{Z}/2).$$
--
--   In degree $2$ this is Tate's relation $\chi_a\cup\chi_{1-a}=0$; in general it follows from it by the associativity of the cup product. Together with multiplicativity in each slot, it shows that the Galois symbol factors through Milnor K-theory.
--
--   **Formalization Note** Adjacency is expressed by indices $i,j$ with $i+1=j$ (as natural numbers), matching the definition of the Steinberg subgroup in `MilnorConjecture_MilnorK`.
-- source:
--   J. Milnor, Algebraic K-theory and quadratic forms, Invent. Math. 9 (1970), 318-344, https://doi.org/10.1007/BF01425486, Section 6 (definition of the homomorphism h_n : K_n F / 2 K_n F -> H^n(F, Z/2))

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol

namespace MilnorConjecture
theorem galoisSymbol_steinberg (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ)
    (a : Fin n → Fˣ) (i j : Fin n) (hij : (i : ℕ) + 1 = j) (h : (a i : F) + (a j : F) = 1) :
    galoisSymbol a = 0 := by sorry
end MilnorConjecture
