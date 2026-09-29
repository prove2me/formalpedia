-- Prove2me | Theorems.Thm_MilnorConjecture_galoisSymbol_update_mul
-- name    : MilnorConjecture.galoisSymbol_update_mul
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T12:05:12.595639+00:00
-- url     : https://prove2.me/theorems/670dcf26-1886-49f5-8ff2-d92179321ab5
-- title:
--   Galois symbol is multiplicative in each slot
-- statement:
--   Let $F$ be a field of characteristic different from $2$, let $F^{\mathrm{sep}}$ be a separable closure and $G_F=\operatorname{Gal}(F^{\mathrm{sep}}/F)$. For $a\in F^\times$ let $\chi_a:G_F\to\mathbb{Z}/2$ be the Kummer character ($\chi_a(\sigma)=0$ iff $\sigma$ fixes a chosen square root of $a$). For $a=(a_1,\dots,a_n)\in(F^\times)^n$, the Galois symbol $\mathrm{gs}(a_1,\dots,a_n)\in H^n(F,\mathbb{Z}/2)$ is the cup product $\chi_{a_1}\cup\cdots\cup\chi_{a_n}$ in continuous Galois cohomology (with $\mathrm{gs}()=1\in H^0$).
--
--   Then the Galois symbol is multiplicative in each argument: for every index $i$ and all $x,y\in F^\times$,
--
--   $$\mathrm{gs}(a_1,\dots,xy,\dots,a_n)=\mathrm{gs}(a_1,\dots,x,\dots,a_n)+\mathrm{gs}(a_1,\dots,y,\dots,a_n),$$
--
--   where $xy$, $x$, $y$ sit in position $i$.
--
--   This is one of the two facts (with the Steinberg relation) needed for the Galois symbol to descend to a homomorphism $K^M_n(F)\to H^n(F,\mathbb{Z}/2)$, the norm residue homomorphism.
--
--   **Formalization Note** Replacing the $i$-th entry is `Function.update a i`; the Galois symbol is the definition `galoisSymbol` of the `MilnorConjecture_GaloisSymbol` bundle.
-- source:
--   J. Milnor, Algebraic K-theory and quadratic forms, Invent. Math. 9 (1970), 318-344, https://doi.org/10.1007/BF01425486, Section 6 (definition of the homomorphism h_n : K_n F / 2 K_n F -> H^n(F, Z/2))

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol

namespace MilnorConjecture
theorem galoisSymbol_update_mul (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ)
    (a : Fin n → Fˣ) (i : Fin n) (x y : Fˣ) :
    galoisSymbol (Function.update a i (x * y)) =
      galoisSymbol (Function.update a i x) + galoisSymbol (Function.update a i y) := by sorry
end MilnorConjecture
